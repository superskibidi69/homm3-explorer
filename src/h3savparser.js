// ============================================================
// HoMM3 Savegame Parser (h3savparser.js)
//
// Supports: .GM1 (singleplayer), .GM2 (hotseat/multiplayer),
//           .TGM (timed), .CGM (campaign)
//
// Format research based on:
//   - heroescommunity.com/viewthread.php3?TID=18817
//   - https://github.com/suurjaak/h3sed
//
// SPDX-License-Identifier: MIT
// Copyright (c) 2026 HoMM3 Explorer Contributors
// ============================================================

const H3Sav = (() => {
    'use strict';

    // ---- Version detection ----

    // Version name based on version_major byte at offset 8 of decompressed data.
    // Ranges taken from h3sed (version modules) and HotA community research.
    function versionName(major, minor) {
        if (major >= 16 && major <= 27) return 'RoE';          // Restoration of Erathia
        if (major >= 28 && major <= 41) return 'AB';           // Armageddon's Blade
        if (major === 42 || major === 43) return 'SoD';        // Shadow of Death
        if (major === 44) {
            // HotA distinguishes sub-versions via minor
            if (minor >= 6) return 'HotA 1.7+';
            if (minor >= 5) return 'HotA 1.6';
            return 'HotA';
        }
        if (major === 51) return 'WoG';                        // Wake of Gods / ERA
        if (major > 44 && major < 51) return 'HotA';
        if (major > 51) return 'ERA';
        return `Unknown (v${major}.${minor})`;
    }

    // ---- Gzip / raw-deflate decompression ----
    //
    // HoMM3 savegames are stored as gzip streams but with an invalid/
    // truncated CRC checksum.  Standard gzip decompressors (including
    // pako in inflate mode) therefore reject the stream.
    //
    // Work-around: skip the gzip header manually, then use pako.inflateRaw
    // which performs raw DEFLATE decoding without validating the gzip footer.

    function skipGzipHeader(data) {
        if (data[0] !== 0x1f || data[1] !== 0x8b) throw new Error('Not a gzip stream');
        const flags = data[3];
        let pos = 10;
        if (flags & 4) { // FEXTRA
            const xlen = data[pos] | (data[pos + 1] << 8);
            pos += 2 + xlen;
        }
        if (flags & 8) { // FNAME – null-terminated
            while (data[pos] !== 0) pos++;
            pos++;
        }
        if (flags & 16) { // FCOMMENT – null-terminated
            while (data[pos] !== 0) pos++;
            pos++;
        }
        if (flags & 2) pos += 2; // FHCRC
        return pos;
    }

    function decompressSave(data) {
        if (!(data instanceof Uint8Array)) data = new Uint8Array(data);
        const payloadStart = skipGzipHeader(data);
        // pako.inflateRaw does raw DEFLATE without gzip wrapper → no CRC check
        return pako.inflateRaw(data.subarray(payloadStart));
    }

    // ---- String extraction helpers ----

    function readLeU16(buf, off) {
        return buf[off] | (buf[off + 1] << 8);
    }

    function readString(buf, off) {
        const len = readLeU16(buf, off);
        if (len === 0) return { str: '', next: off + 2 };
        const bytes = buf.subarray(off + 2, off + 2 + len);
        let str;
        try { str = new TextDecoder('windows-1252').decode(bytes); } catch { str = new TextDecoder('latin1').decode(bytes); }
        return { str, next: off + 2 + len };
    }

    // Check whether a uint8 is printable Latin-1.
    function isPrintable(b) {
        return (b >= 0x20 && b < 0x7f) || b >= 0xa0;
    }

    // Locate the map-name/description strings in the decompressed savegame.
    //
    // The layout of the savegame header differs slightly between game versions,
    // so we use a heuristic scanner rather than hard-coded offsets.
    //
    // Pattern: scan bytes 20–300 for a LE uint16 (1–200) followed by exactly
    // that many printable-Latin-1 bytes, directly followed by another LE uint16
    // (0–2000) that can be 0.  The first hit is the name; the next field is the
    // description.
    function findNameDesc(buf) {
        const searchEnd = Math.min(buf.length - 10, 400);
        for (let i = 20; i < searchEnd; i++) {
            const nlen = readLeU16(buf, i);
            if (nlen < 1 || nlen > 200) continue;
            if (i + 2 + nlen + 2 > buf.length) continue;
            // All name bytes must be printable
            let ok = true;
            for (let j = 0; j < nlen; j++) {
                if (!isPrintable(buf[i + 2 + j])) { ok = false; break; }
            }
            if (!ok) continue;
            // Followed by a plausible description length
            const dpos = i + 2 + nlen;
            const dlen = readLeU16(buf, dpos);
            if (dlen > 4000) continue;
            // Validate description bytes (allow 0-length)
            if (dlen > 0) {
                let dok = true;
                for (let j = 0; j < Math.min(dlen, 30); j++) {
                    if (dpos + 2 + j >= buf.length) { dok = false; break; }
                    // Allow a wider range for descriptions (may contain special chars)
                    const b = buf[dpos + 2 + j];
                    if (b < 0x09) { dok = false; break; } // no control chars except tab/LF/CR
                }
                if (!dok) continue;
            }
            // Found!
            let name = '';
            try { name = new TextDecoder('windows-1252').decode(buf.subarray(i + 2, i + 2 + nlen)); }
            catch { name = new TextDecoder('latin1').decode(buf.subarray(i + 2, i + 2 + nlen)); }
            let desc = '';
            if (dlen > 0) {
                try { desc = new TextDecoder('windows-1252').decode(buf.subarray(dpos + 2, dpos + 2 + dlen)); }
                catch { desc = new TextDecoder('latin1').decode(buf.subarray(dpos + 2, dpos + 2 + dlen)); }
            }
            return { name, desc };
        }
        return { name: '', desc: '' };
    }

    // ---- Savegame map-header extraction ----
    //
    // The savegame binary contains map metadata (version, size, name, etc.)
    // starting at a fixed offset within the first decompressed stream.
    // The layout DIFFERS from a standalone .h3m file: there are 12 extra
    // savegame-specific bytes between the version uint32 and the mapSize uint32.
    //
    // Known H3M version codes: 14 (RoE), 21 (AB), 28 (SoD), 29 (Chr), 32 (HotA), 51 (WoG)
    const H3M_VERSIONS = new Set([14, 21, 28, 29, 32, 51]);

    // H3M version code → human-readable name
    const H3M_VERSION_NAMES = { 14: 'RoE', 21: 'AB', 28: 'SoD', 29: 'SoD/Chr', 32: 'HotA', 51: 'WoG/ERA' };

    // Map size code → label
    const MAP_SIZE_LABELS = { 36: 'S', 72: 'M', 108: 'L', 144: 'XL', 216: 'H', 252: 'XH' };

    /**
     * Parse the embedded map header from a decompressed savegame buffer.
     *
     * Layout (confirmed empirically for 111.GM1 HotA):
     *   dec[0x34..0x38]  h3mVersion (4 bytes LE) — same as standalone .h3m
     *   dec[0x38..0x3e]  6 savegame-specific bytes (turn counter, speed, etc.)
     *   dec[0x3e..0x40]  2 more savegame bytes
     *   dec[0x40..0x44]  mapSize (4 bytes LE) — e.g. 72 for Medium
     *   dec[0x44]        hasUnderground (1 byte)
     *   dec[0x45..0x49]  nameLen (4 bytes LE) — length of the GERMAN/localised map name
     *   dec[0x49..]      name string (nameLen bytes, windows-1252)
     *   (then descLen + desc)
     *
     * The base offset 0x34 is invariant for all SoD/HotA savegames tested; it
     * may differ for RoE/AB saves (which use 0x30).
     *
     * @param {Uint8Array} dec  Decompressed savegame data.
     * @returns {object|null}  Map header fields or null on parse error.
     */
    function parseSavegameMapHeader(dec) {
        // Find the version uint32 first (scan 0x28..0x44)
        let vOff = null;
        for (let i = 0x28; i <= 0x60; i++) {
            const v = (dec[i] | (dec[i+1]<<8) | (dec[i+2]<<16) | (dec[i+3]<<24)) >>> 0;
            if (H3M_VERSIONS.has(v)) { vOff = i; break; }
        }
        if (vOff === null) return null;

        try {
            const h3mVersion = (dec[vOff] | (dec[vOff+1]<<8) | (dec[vOff+2]<<16) | (dec[vOff+3]<<24)) >>> 0;
            // Extra savegame bytes: 12 bytes between version and mapSize (confirmed)
            const mapSizeOff = vOff + 4 + 8; // skip 8 extra bytes
            const mapSize = (dec[mapSizeOff] | (dec[mapSizeOff+1]<<8) | (dec[mapSizeOff+2]<<16) | (dec[mapSizeOff+3]<<24)) >>> 0;
            const hasUnderground = dec[mapSizeOff + 4] !== 0;
            // Read map name (locale name, stored as 4-byte-len-prefixed string)
            const nameLenOff = mapSizeOff + 5;
            const nameLen = (dec[nameLenOff] | (dec[nameLenOff+1]<<8) | (dec[nameLenOff+2]<<16) | (dec[nameLenOff+3]<<24)) >>> 0;
            let mapName = '';
            if (nameLen > 0 && nameLen < 500) {
                mapName = new TextDecoder('windows-1252').decode(dec.subarray(nameLenOff + 4, nameLenOff + 4 + nameLen));
            }
            // Validate: mapSize must be a reasonable map size
            if (mapSize < 18 || mapSize > 512 || nameLen > 500) return null;
            return {
                h3mVersion,
                h3mVersionName: H3M_VERSION_NAMES[h3mVersion] || `v${h3mVersion}`,
                mapSize,
                mapSizeLabel: MAP_SIZE_LABELS[mapSize] || `${mapSize}×${mapSize}`,
                hasUnderground,
                mapName,
            };
        } catch (e) {
            return null;
        }
    }

    // Legacy: find offset of H3M version code (kept for backward compat)
    function findEmbeddedOffset(dec) {
        for (let i = 0x28; i <= 0x44; i++) {
            const v = dec[i] | (dec[i+1] << 8) | (dec[i+2] << 16) | (dec[i+3] << 24);
            if (H3M_VERSIONS.has(v >>> 0)) return i;
        }
        return null;
    }

    // ---- Map filename extraction ----
    //
    // The original map/campaign filename (e.g. "[HotA] Air Supremacy.h3m") is
    // stored as a null-terminated ASCII string in the first ~2000 bytes of the
    // decompressed savegame.  We search for the extension pattern.

    function findMapFilename(dec) {
        const head = new TextDecoder('latin1').decode(dec.subarray(0, Math.min(dec.length, 2000)));
        const m = head.match(/([\[A-Za-z0-9][^\x00-\x1f\x7f]{2,}\.h3[mc])/i);
        return m ? m[1].trim() : null;
    }

    // ---- Hero game-data constants ----

    const PLAYER_COLORS = ['Red', 'Blue', 'Tan', 'Green', 'Orange', 'Purple', 'Teal', 'Pink'];

    const SKILL_NAMES = [
        'Pathfinding','Archery','Logistics','Scouting','Diplomacy','Navigation','Leadership',
        'Wisdom','Mysticism','Luck','Ballistics','Eagle Eye','Necromancy','Estates',
        'Fire Magic','Air Magic','Water Magic','Earth Magic','Scholar','Tactics',
        'Artillery','Learning','Offense','Armorer','Intelligence','Sorcery',
        'Resistance','First Aid'
    ];
    const SKILL_LEVEL_NAMES = ['', 'Basic', 'Advanced', 'Expert'];

    // Creature IDs (index = creature ID, HoMM3 SoD + HotA ordering)
    const CREATURE_NAMES = [
        'Pikeman','Halberdier','Archer','Marksman','Griffin','Royal Griffin','Swordsman','Crusader',
        'Monk','Zealot','Cavalier','Champion','Angel','Archangel',                                   // Castle 0-13
        'Centaur','Centaur Captain','Dwarf','Battle Dwarf','Wood Elf','Grand Elf','Pegasus','Silver Pegasus',
        'Dendroid Guard','Dendroid Soldier','Unicorn','War Unicorn','Green Dragon','Gold Dragon',      // Rampart 14-27
        'Gremlin','Master Gremlin','Stone Gargoyle','Obsidian Gargoyle','Stone Golem','Iron Golem',
        'Mage','Arch Mage','Genie','Master Genie','Naga','Naga Queen','Giant','Titan',               // Tower 28-41
        'Imp','Familiar','Gog','Magog','Hell Hound','Cerberus','Demon','Horned Demon',
        'Pit Fiend','Pit Lord','Efreet','Efreet Sultan','Devil','Arch Devil',                        // Inferno 42-55
        'Skeleton','Skeleton Warrior','Walking Dead','Zombie','Wight','Wraith','Vampire','Vampire Lord',
        'Lich','Power Lich','Black Knight','Dread Knight','Bone Dragon','Ghost Dragon',              // Necropolis 56-69
        'Gnoll','Gnoll Marauder','Lizardman','Lizard Warrior','Serpent Fly','Dragon Fly',
        'Basilisk','Greater Basilisk','Gorgon','Mighty Gorgon','Wyvern','Wyvern Monarch',
        'Hydra','Chaos Hydra',                                                                        // Dungeon 70-83
        'Troglodyte','Infernal Troglodyte','Harpy','Harpy Hag','Beholder','Evil Eye',
        'Medusa','Medusa Queen','Minotaur','Minotaur King','Manticore','Scorpicore',
        'Red Dragon','Black Dragon',                                                                  // Dungeon (Dark) 84-97 — same slot
        'Goblin','Hobgoblin','Wolf Rider','Wolf Raider','Orc','Orc Chieftain',
        'Ogre','Ogre Mage','Roc','Thunderbird','Cyclops','Cyclops King','Behemoth','Ancient Behemoth', // Stronghold 84-97
        'Gnoll','Gnoll Marauder','Lizardman','Lizard Warrior','Serpent Fly','Dragon Fly',
        'Basilisk','Greater Basilisk','Gorgon','Mighty Gorgon','Wyvern','Wyvern Monarch','Hydra','Chaos Hydra',
        'Sprite','Pixie','Air Elemental','Storm Elemental','Water Elemental','Ice Elemental',
        'Fire Elemental','Energy Elemental','Earth Elemental','Magma Elemental',
        'Psyemental','Magic Elemental','Firebird','Phoenix',                                          // Conflux area
        'Halfling','Peasant','Boar','Mummy','Nomad','Rogue','Troll',                                 // Neutral 112-118
    ];
    function creatureName(id) {
        if (id === 0xFFFFFFFF || id < 0) return null;
        return CREATURE_NAMES[id] || `Creature#${id}`;
    }

    // ---- Hero struct scanner ----
    //
    // Hero structs are stored in the decompressed savegame (all heroes in the
    // game, including neutral/unowned ones).  Each struct is ~1154 bytes.
    // Key offsets (from h3sed metadata.py, HERO_BYTE_POSITIONS):
    //
    //   0:   faction (0-7 = Red..Pink, 255 = neutral/not hired)
    //  31:   movement_total  (4 bytes LE)
    //  35:   movement_left   (4 bytes LE)
    //  39:   experience      (4 bytes LE)
    //  43:   skills_count    (4 bytes LE)
    //  47:   mana_left       (2 bytes LE)
    //  49:   level           (1 byte)
    // 113:   army_types      (7 × 4-byte LE creature IDs)
    // 141:   army_counts     (7 × 4-byte LE counts)
    // 169:   name            (13 bytes, first byte printable ASCII, null-padded)
    // 182:   skill_levels    (28 bytes, values 0-3)
    // 210:   skill_slots     (28 bytes, values 0-27)
    // 238:   attack          (1 byte)
    // 239:   defense         (1 byte)
    // 240:   spell_power     (1 byte)
    // 241:   knowledge       (1 byte)
    // 242:   spells_in_book  (70 bytes, 0/1)
    // 312:   spells_avail    (70 bytes, 0/1)

    function extractHeroes(dec, encoding = 'windows-1252') {
        const heroes = [];
        // Pattern: find candidate hero-name positions (13 bytes: capital letter + ≤12 chars + null)
        // then validate the struct fields around it.
        for (let namePos = 169; namePos < dec.length - 600; namePos++) {
            const b0 = dec[namePos];
            // First byte must be uppercase letter or common name start
            if (b0 < 0x41 || b0 > 0x5a) continue;
            // 13th byte must be null
            if (dec[namePos + 12] !== 0x00) continue;
            // Bytes 1-11 must be alpha (A-Za-z) or null; at least one lowercase.
            // HoMM3 hero names are purely alphabetic — no digits, dots, hyphens, etc.
            let nameOk = false, hasLower = false;
            for (let j = 1; j < 12; j++) {
                const c = dec[namePos + j];
                if (c === 0) break;  // null terminator
                const isUpper = c >= 0x41 && c <= 0x5a;
                const isLower = c >= 0x61 && c <= 0x7a;
                if (!isUpper && !isLower) { nameOk = false; break; }
                if (isLower) hasLower = true;
                nameOk = true;
            }
            if (!nameOk || !hasLower) continue;

            // This is a candidate name.  Derive struct start.
            const s = namePos - 169;
            if (s < 0) continue;
            if (s + 382 > dec.length) continue;

            // Validate skill_levels[182..209] (all 0-3) and skill_slots[210..237] (all 0-27)
            let skillOk = true;
            for (let j = 0; j < 28; j++) {
                if (dec[s + 182 + j] > 3 || dec[s + 210 + j] > 27) { skillOk = false; break; }
            }
            if (!skillOk) continue;

            // Faction at offset 0 (0-7 = active player, 255 = neutral)
            const faction = dec[s + 0];
            if (faction !== 0xff && faction > 7) continue;

            // Extract name
            let nameEnd = namePos;
            while (nameEnd < namePos + 13 && dec[nameEnd] !== 0) nameEnd++;
            const nameStr = new TextDecoder(encoding).decode(dec.subarray(namePos, nameEnd));

            // Primary stats
            const level  = dec[s + 49];
            const attack = dec[s + 238];
            const defense= dec[s + 239];
            const power  = dec[s + 240];
            const knowledge= dec[s + 241];
            const exp    = (dec[s+39] | (dec[s+40]<<8) | (dec[s+41]<<16) | (dec[s+42]<<24)) >>> 0;
            const mana   = dec[s+47] | (dec[s+48]<<8);
            const movTotal  = (dec[s+31]|(dec[s+32]<<8)|(dec[s+33]<<16)|(dec[s+34]<<24))>>>0;
            const movLeft   = (dec[s+35]|(dec[s+36]<<8)|(dec[s+37]<<16)|(dec[s+38]<<24))>>>0;

            // Reject implausible primary stats (sane game caps)
            if (attack > 99 || defense > 99 || power > 99 || knowledge > 99) continue;
            if (level > 108) continue; // max level in any mod
            if (exp > 2_000_000_000) continue; // unsigned wrap or garbage

            // Army
            const army = [];
            for (let slot = 0; slot < 7; slot++) {
                const tid = (dec[s+113+slot*4]|(dec[s+114+slot*4]<<8)|(dec[s+115+slot*4]<<16)|(dec[s+116+slot*4]<<24))>>>0;
                const cnt = (dec[s+141+slot*4]|(dec[s+142+slot*4]<<8)|(dec[s+143+slot*4]<<16)|(dec[s+144+slot*4]<<24))>>>0;
                // cnt sanity: 0 = empty, >500000 = garbage (no sane army that large)
                if (tid < 0xFFFFFFFE && cnt > 0 && cnt <= 500_000) army.push({ id: tid, name: creatureName(tid), count: cnt });
            }

            // Skills: skill_levels[182..209] is indexed by skill ID (0-27),
            // value = Stufe (0=keine, 1=Basic, 2=Advanced, 3=Expert).
            // skill_slots[210..237] enthalten in Savegames nur Nullen → ignorieren.
            const skills = [];
            for (let i = 0; i < 28; i++) {
                const lvl = dec[s + 182 + i];
                if (lvl > 0 && lvl <= 3) {
                    skills.push({ name: SKILL_NAMES[i], level: SKILL_LEVEL_NAMES[lvl] || String(lvl) });
                }
            }

            heroes.push({
                structOffset: s,
                name: nameStr,
                faction,
                factionName: faction < 8 ? PLAYER_COLORS[faction] : 'Neutral',
                level, attack, defense, power, knowledge,
                exp, mana, movTotal, movLeft,
                army, skills,
            });

            // Skip to avoid re-matching inside same struct (struct ~1154 bytes)
            namePos += 1153;
        }
        return heroes;
    }

    /**
     * Filter a hero list to only include heroes that appear to be genuinely
     * active/hired (not slot-filler / uninitialized entries or map-name false positives).
     *
     * A hero is considered "active" when:
     *  - faction is a valid player (0-7)
     *  - AND at least one of: exp > 0, level > 0, movTotal > 0, army not empty,
     *    skills not empty.  (All-zero entries are uninitialized database slots.)
     */
    function filterActiveHeroes(heroes) {
        return heroes.filter(h => {
            if (h.faction >= 8) return false; // neutral / unowned
            // Must have some sign of being a real hero on the map
            return h.exp > 0 || h.level > 0 || h.movTotal > 0 || h.army.length > 0 || h.skills.length > 0;
        });
    }

    // ---- Main parse entry point ----

    /**
     * Parse a HoMM3 savegame file.
     *
     * @param {Uint8Array} data  Raw (compressed) savegame bytes.
     * @param {string}     ext   File extension lowercase: 'gm1','gm2','tgm','cgm'.
     * @returns {object}  Parsed savegame metadata.
     */
    function parseSavegame(data, ext) {
        if (!(data instanceof Uint8Array)) data = new Uint8Array(data);

        let dec;
        try {
            dec = decompressSave(data);
        } catch (e) {
            throw new Error(`Failed to decompress savegame: ${e.message}`);
        }

        if (dec.length < 16) throw new Error('Decompressed data too short');

        // Magic
        const magic = String.fromCharCode(dec[0], dec[1], dec[2], dec[3], dec[4]);
        if (magic !== 'H3SVG' && magic !== 'H3SVC') {
            throw new Error(`Invalid savegame magic: ${magic}`);
        }

        const isCampaignSave = (magic === 'H3SVC');
        const saveType = ext === 'cgm' ? 'Campaign Save (.CGM)'
                       : ext === 'gm2' ? 'Multiplayer Save (.GM2)'
                       : ext === 'tgm' ? 'Timed Game Save (.TGM)'
                       : 'Singleplayer Save (.GM1)';

        const versionMajor = dec[8];
        const versionMinor = dec[12];
        const verName = versionName(versionMajor, versionMinor);

        // Name + description (heuristic scan)
        const { name, desc } = findNameDesc(dec);

        // Embedded map / campaign data
        // NOTE: embeddedMapData is NOT a standalone .h3m file — the savegame
        // interleaves extra state bytes with the H3M header.  Use mapHeader
        // (below) to get the map metadata, and embeddedMapData only when you
        // have a custom savegame-aware parser.
        const embeddedOffset = findEmbeddedOffset(dec);
        const embeddedMapData = embeddedOffset != null ? dec.subarray(embeddedOffset) : null;

        // Parse the embedded map header directly from the savegame buffer.
        const mapHeader = parseSavegameMapHeader(dec);

        // Map filename (null-terminated, found in first ~2000 decompressed bytes)
        const mapFilename = findMapFilename(dec);

        // Hero list (scans full decompressed data; may be slow for huge saves)
        const heroes = extractHeroes(dec);

        return {
            magic,
            isCampaignSave,
            saveType,
            ext: ext || '',
            versionMajor,
            versionMinor,
            versionName: verName,
            name: name || '',
            description: desc || '',
            compressedSize: data.length,
            decompressedSize: dec.length,
            embeddedMapData,   // Uint8Array — NOT directly parseable as .h3m (has extra savegame bytes)
            embeddedOffset,    // numeric byte offset or null
            mapHeader,         // parsed map metadata: { h3mVersion, mapSize, mapSizeLabel, hasUnderground, mapName }
            mapFilename,       // e.g. "[HotA] Air Supremacy.h3m" or null
            heroes,            // array of hero objects (all heroes in the game database)
            activeHeroes: filterActiveHeroes(heroes),
            _decompressed: dec,
        };
    }

    // ---- Public API ----
    return {
        /** Parse a HoMM3 savegame Uint8Array.  Returns a savegame metadata object. */
        parseSavegame,
        /** Decompress a savegame (raw-deflate, ignores invalid CRC). */
        decompressSave,
        /** Detect version name from major/minor bytes. */
        versionName,
        /** Extract hero list from a decompressed savegame buffer. */
        extractHeroes,
        /** Filter hero list to only genuinely active/hired heroes. */
        filterActiveHeroes,
        /** Parse the embedded map header from a decompressed savegame buffer. */
        parseSavegameMapHeader,
        /** Human-readable player color names indexed 0-7. */
        PLAYER_COLORS,
        SKILL_NAMES,
        SKILL_LEVEL_NAMES,
        creatureName,
    };
})();
