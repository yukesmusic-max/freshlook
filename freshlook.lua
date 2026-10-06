-- A new home for norns. 
-- A fully-customizable
-- tag-based browser
-- includes tutorial and tool tips
-- Made with love 
-- by Yukes, Shanghai

local tabutil = require 'tabutil'
local textentry = require 'textentry'
local json = include('lib/json')

-- Source of truth: `categories` defines the taxonomy (category name -> ordered
-- list of subcategory names), `scripts` is every known script keyed by its raw
-- name (folder, or 'folder/file' for a family folder), each with its own
-- category/subcategory assignment ("" means not yet assigned to that level).
-- Everything the browse screen renders (`data`/`keys` below) is DERIVED from
-- these two tables by rebuild_browse_view(), never edited directly.
local categories = {}
local scripts = {}
-- Snapshot of `categories` taken by "Delete all categories and subcategories",
-- consumed (but not cleared -- it's safe to restore more than once) by
-- "Restore all categories and subcategories". Persisted in data.json.
local deleted_categories_backup = nil
-- True once the onboarding tutorial has run its course (finished, declined
-- on slide 1, or ended early via K1 long-press) -- see save_fresh_data's
-- own comment for why this lives here instead of the opt_show_tutorial
-- pset. This is the real gate at init() time; the param just mirrors it
-- for the Functions screen's own display/toggle.
local tutorial_seen = false

-- Derived view for the browse screen, rebuilt from categories+scripts by
-- rebuild_browse_view() below whenever either changes:
-- data[category][subcategory] = {{name, description, is_favorite}, ...}, or
-- data[category] = {...} directly for a flat (no-subcategory) node.
local data = {}
local keys = {}

local faves = tabutil.load(_path.favorites)
if faves == nil then
  faves = {}
  tabutil.save(faves, _path.favorites)
end

local mode = 'browse' -- 'browse' | 'menu' | 'sort_menu' | 'sort_options' | 'sort' | 'categories' | 'settings' | 'tutorial' | 'replace_home' | 'tooltip'
-- Set while the "Show Script Info on Load" preview prompt is up (K3 confirms
-- and loads, K2 cancels back to browsing instead of jumping to nav_back_pos).
local browse_confirm = false
local selection = nil
local last_favorite_time = 0
local nav_back_pos = 0
local k1_press_time = nil
local k2_press_time = nil
local LONG_PRESS_SEC = 0.5

--- Linear view mode (View Mode option 3): a menu-dive through category ->
--- subcategory -> scripts instead of one long scrolling list.
local linear_step = 1 -- 1 = categories, 2 = subcategories, 3 = scripts
local linear_pos = 1 -- 1-based selected index into the current level's rows
local linear_category = nil
local linear_subcategory = nil -- nil at step 3 for a flat (no-subcategory) category

local type_size = 8
local line_height = math.ceil(type_size * 1.25)
local space_width = math.ceil(type_size * 0.5)

local entry_x = 1
local desc_x = 64 + (space_width * 2)

local nav_fav_x = 100
local nav_total_x = 122 -- right-hugging "#" column, clear of the scrollbar at x=127
local nav_label_len = type_size * 1.6 + 2 -- a bit more room now that the columns moved right

local card_height = 6
local full_title_font = 12
local full_title_line_height = math.ceil(full_title_font * 1.3)
local full_title_wrap_chars = 15
local full_desc_wrap_chars = 22

-- No personal shortcuts baked in -- a fresh install starts with none pinned.
local pinned_scripts = {}

--- Menu (long-press K1)
local menu_pos = 1
local menu_options = { 'View', 'Functions', 'Sort Scripts' }

--- Settings screen state
local settings_pos = 0
local settings_selection = nil
local settings_confirm = nil -- true while the Alphabetize Favorites prompt is up
-- Brief "favorites sorted" feedback -- rendered by redraw_settings itself and
-- cleared on a timer, since the dispatcher's own trailing redraw() would
-- otherwise immediately overwrite anything drawn via the shared show_message.
local settings_message = nil

--- Onboarding tutorial state (first boot only, or re-triggered via Functions)
local tutorial_index = 1
-- True once the user has started stepping back with K2 -- kept true across
-- further K2 presses so a run of "back" keeps retreating through a slide's
-- own special K2 meaning (a Yes/No prompt, End Tutorial, Disable Now, a
-- hidden K2) instead of triggering it; K3 (moving forward again) clears it.
local tutorial_backing = false
-- nil | 'autosort_results'
local tutorial_substate = nil
local tutorial_autosort_results = nil -- { assigned, already, remain }, set after the tutorial's own auto-sort step
-- E3 scroll offset for an `outline: true` slide (the only slide kind that
-- uses E3 at all) -- reset to 0 on every slide change, see tutorial_advance
-- / tutorial_step_back.
local tutorial_outline_pos = 0

--- Tool tip state -- fires from Settings right after flipping a toggle or
--- selecting an action, same slide-engine style as the tutorial. `tooltip_row`
--- is the settings row def that triggered it (its `.tip` key looks up the
--- windows in TOOLTIPS, its `.id` is what "enable"/"disable" below act on).
local tooltip_row = nil
local tooltip_index = 1
-- nil | 'backup_result'
local tooltip_substate = nil
local tooltip_backup_filename = nil
-- Both forward-declared: real content/definition come later (near the rest
-- of the tool tip engine), but enc_settings/key_settings call tooltip_for
-- earlier in the file than that, so it (and the table it reads) need to
-- already exist as upvalues by then.
local TOOLTIPS = {}
local tooltip_for

--- "Replace Home Screen" guide state (reached from Functions) -- same
--- slide-engine style as the onboarding tutorial, its own short sequence.
local replace_home_index = 1

--- Sort Scripts menu state (Auto Sort / Manual Sort / Reset Sorting)
local sort_menu_pos = 1
local sort_menu_options = { 'Auto Sort', 'Manual Sort', 'Define Categories', 'Reset Sorting !!' }
-- nil | 'confirm_auto' | 'results' | 'confirm_reset'
local sort_menu_state = nil
local sort_menu_results = nil -- { assigned, already, remain }, set after auto-sort

--- Manual Sort options (pre-screen before the actual list)
local sort_options_pos = 1
-- "Only show unsorted scripts in this list" -- same idea as the old "hide
-- sorted" filter, just the question asked the other way around.
local sort_hide_sorted = false
-- Rejected scripts always stay in the Sort Scripts list by default (dimmed,
-- with a [REJECTED] marker) so they can still be found and categorized; this
-- just lets you filter them out of view entirely once you're done with them.
local sort_show_rejected = true

--- Define Categories state
local cat_pos = 0
local cat_selection = nil
local cat_confirm = nil -- { message, on_confirm, on_decline }
-- Brief result feedback (e.g. after Delete All) -- same reasoning as
-- settings_message: the dispatcher's own trailing redraw() would otherwise
-- immediately overwrite anything drawn via the shared show_message.
local cat_message = nil

----------------------------------------------------------------------------
-- Shared helpers -- small text/screen utilities used throughout the rest
-- of this file.
----------------------------------------------------------------------------

--- Print truncated text to screen, if longer than length add '...'
local function text_trunc(str, len)
  len = math.floor(len) or 10
  local trunc = ''

  if str ~= nil then
    trunc = string.sub(str, 1, len)
    if #str > #trunc then
      trunc = trunc .. '...'
    end
  end

  trunc = trunc:gsub('^%s*(.-)%s*$', '%1')
  screen.text(trunc)

  return trunc
end

local function titlecase(text)
  return text:gsub('^%l', string.upper)
end

--- Greedy word-wrap: splits `text` into lines of at most `max_chars` characters.
local function wrap_text(text, max_chars)
  local lines = {}
  local current = ''
  for word in (text or ''):gmatch('%S+') do
    local candidate = (current == '') and word or (current .. ' ' .. word)
    if #candidate <= max_chars then
      current = candidate
    else
      if current ~= '' then
        table.insert(lines, current)
        current = ''
      end
      while #word > max_chars do
        table.insert(lines, word:sub(1, max_chars))
        word = word:sub(max_chars + 1)
      end
      current = word
    end
  end
  if current ~= '' or #lines == 0 then
    table.insert(lines, current)
  end
  return lines
end

--- A category value is either a flat array of entries, or a map of subcategory
--- name -> array of entries (an empty {} is ambiguous either way, treat as flat).
local function is_subcategory_map(t)
  return t[1] == nil and next(t) ~= nil
end

--- True when a "yes"/"no" Launcher Options param is set to "yes" (option index 1).
local function opt_on(id)
  return params:get(id) == 1
end

--- True when the "View Mode" option is set to "Expanded" (option index 2).
--- Expanded view pages through the full list one script at a time -- that only makes
--- sense when the full list is actually reachable. When "Full List After Nav" is
--- off, treat View Mode as Compact regardless of what's selected, so toggling
--- either option can never leave the screen trying to page cards that aren't
--- there (which showed up as a black screen) -- Quick Nav always stays visible.
local function is_full_view()
  return params:get("opt_view_mode") == 2 and opt_on("opt_show_full_after_nav")
end

--- For a "family" folder that bundles several independent scripts, a script's
--- raw name is 'folder/file'; only the part after the '/' is shown.
local function display_name(name)
  return name:match('([^/]+)$') or name
end

--- Resolve a raw script name to its actual .lua file: exact folder/folder.lua
--- match -> case-insensitive match -> the only .lua file present, if just one.
local function resolve_script_file(name)
  local folder, base = name:match('^(.+)/(.+)$')
  if folder then
    local file = _path.code .. folder .. '/' .. base .. '.lua'
    if util.file_exists(file) then
      return file
    end
    return nil, name .. ' not found'
  end

  local dir = _path.code .. name .. '/'
  local exact = dir .. name .. '.lua'
  if util.file_exists(exact) then
    return exact
  end

  local candidates = {}
  for _, fname in ipairs(util.scandir(dir)) do
    if fname:match('%.lua$') then
      table.insert(candidates, fname)
    end
  end

  local lower_target = name:lower() .. '.lua'
  for _, fname in ipairs(candidates) do
    if fname:lower() == lower_target then
      return dir .. fname
    end
  end

  if #candidates == 1 then
    return dir .. candidates[1]
  elseif #candidates == 0 then
    return nil, 'no .lua file found in ' .. name
  else
    return nil, name .. ' has ' .. #candidates .. ' scripts, none named ' .. name .. '.lua'
  end
end

--- Reads a script's own header comment for its description, the same convention
--- norns' own preview screen uses: the first non-blank '--' comment line.
local function read_description(path)
  local f = io.open(path, 'rb')
  if not f then return '' end

  local desc = ''
  for _ = 1, 8 do
    local line = f:read('*line')
    if not line then break end
    local content = line:match('^%-%-+%s*(.*)$')
    if content and content ~= '' then
      desc = content
      break
    end
  end
  f:close()
  return desc
end

--- Scans _path.code for every installed script, the same way norns' own SELECT
--- screen would: one entry per folder normally (named for the folder), or one
--- entry per .lua file ('folder/file') for a family folder that bundles several
--- unrelated scripts together. Returns { name = description }.
local function discover_scripts()
  local found = {}

  for _, entry in ipairs(util.scandir(_path.code)) do
    local folder = entry:match('^(.+)/$')
    if folder then
      local dir = _path.code .. folder .. '/'
      local lua_files = {}
      for _, fname in ipairs(util.scandir(dir)) do
        if fname:match('%.lua$') then
          table.insert(lua_files, fname)
        end
      end

      if #lua_files == 1 then
        found[folder] = read_description(dir .. lua_files[1])
      elseif #lua_files > 1 then
        for _, fname in ipairs(lua_files) do
          local base = fname:match('^(.+)%.lua$')
          found[folder .. '/' .. base] = read_description(dir .. fname)
        end
      end
    end
  end

  return found
end

--- Adds any script found on disk that isn't already known, and refreshes
--- descriptions for existing ones -- never touches an existing category/
--- subcategory assignment, and never removes a script that's gone missing.
local function merge_discovered_scripts()
  for name, desc in pairs(discover_scripts()) do
    if scripts[name] then
      scripts[name].description = desc
    else
      scripts[name] = { description = desc, category = '', subcategory = '', rejected = false }
    end
  end
end

local function show_message(text)
  screen.clear()
  screen.level(15)
  local lines = {}
  for line in (text .. '\n'):gmatch('(.-)\n') do table.insert(lines, line) end
  local y = 32 - (math.floor(#lines / 2) * line_height)
  for _, line in ipairs(lines) do
    screen.move(64, y)
    screen.text_center(line)
    y = y + line_height
  end
  screen.update()
  clock.run(function() clock.sleep(2) redraw() end)
end

local function favorite_entry(name, file)
  return { name = name, file = file, path = _path.code .. name .. '/' }
end

local function favorites_index_of(file)
  for i, v in pairs(faves) do
    if v.file == file then return i end
  end
  return nil
end

local function add_favorite(name)
  local file = resolve_script_file(name)
  if not file then return end

  local entry = favorite_entry(name, file)
  if not favorites_index_of(entry.file) then
    table.insert(faves, entry)
    tabutil.save(faves, _path.favorites)
  end
end

local function remove_favorite(name)
  local file = resolve_script_file(name)
  if not file then return end

  local i = favorites_index_of(file)
  if i then
    table.remove(faves, i)
    tabutil.save(faves, _path.favorites)
  end
end

--- Tags each entry with entry[3] = is_favorite, optionally floating favorites
--- to the front of the list (Favorites at Top).
local function float_favorites(list, favorite_names, reorder)
  if not reorder then
    for _, entry in ipairs(list) do
      entry[3] = favorite_names[entry[1]] or false
    end
    return list
  end

  local favs, rest = {}, {}
  for _, entry in ipairs(list) do
    entry[3] = favorite_names[entry[1]] or false
    if entry[3] then
      table.insert(favs, entry)
    else
      table.insert(rest, entry)
    end
  end
  local merged = {}
  for _, e in ipairs(favs) do table.insert(merged, e) end
  for _, e in ipairs(rest) do table.insert(merged, e) end
  return merged
end

--- Total number of script entries under a category or subcategory node.
local function count_entries(node)
  if is_subcategory_map(node) then
    local total = 0
    for _, list in pairs(node) do total = total + #list end
    return total
  end
  return #node
end

--- Number of favorited entries (entry[3] == true) under a category or subcategory node.
local function count_favorites(node)
  local function count_list(list)
    local total = 0
    for _, entry in ipairs(list) do
      if entry[3] then total = total + 1 end
    end
    return total
  end

  if is_subcategory_map(node) then
    local total = 0
    for _, list in pairs(node) do total = total + count_list(list) end
    return total
  end
  return count_list(node)
end

--- Sort subcategory names alphabetically, but always push 'Unsorted' to the end.
local function sort_subkeys(subkeys)
  table.sort(subkeys, function(a, b)
    local a_u = a:lower() == 'unsorted'
    local b_u = b:lower() == 'unsorted'
    if a_u ~= b_u then return b_u end
    return a:lower() < b:lower()
  end)
end

local function visible_subkeys(node)
  local hide_empty = opt_on('opt_hide_empty')
  local subkeys = {}
  for sk, list in pairs(node) do
    if not hide_empty or #list > 0 then
      table.insert(subkeys, sk)
    end
  end
  sort_subkeys(subkeys)
  return subkeys
end

--- Always-non-empty version, ignoring the "Hide Empty Categories" option --
--- for the full list's own content, which has no reason to ever show a
--- (sub)category with nothing scrollable in it (dead blank space, header
--- changing for nothing). The option only governs what Quick Nav lists.
local function nonempty_subkeys(node)
  local subkeys = {}
  for sk, list in pairs(node) do
    if #list > 0 then table.insert(subkeys, sk) end
  end
  sort_subkeys(subkeys)
  return subkeys
end

--- `keys`, filtered to drop empty categories when "Hide Empty Categories" is on.
--- Used only by Quick Nav -- the full list's own content always filters empty
--- (sub)categories regardless (see nonempty_keys below).
local function visible_keys()
  if not opt_on('opt_hide_empty') then return keys end
  local vis = {}
  for _, k in ipairs(keys) do
    if count_entries(data[k]) > 0 then table.insert(vis, k) end
  end
  return vis
end

--- Always-non-empty version of the above, for the full list's own content.
local function nonempty_keys()
  local vis = {}
  for _, k in ipairs(keys) do
    if count_entries(data[k]) > 0 then table.insert(vis, k) end
  end
  return vis
end

--- Finds an entry by name anywhere in `data`.
local function find_entry(name)
  for _, node in pairs(data) do
    if is_subcategory_map(node) then
      for _, list in pairs(node) do
        for _, e in ipairs(list) do
          if e[1] == name then return e end
        end
      end
    elseif type(node) == 'table' then
      for _, e in ipairs(node) do
        if e[1] == name then return e end
      end
    end
  end
  return nil
end

--- Favorited scripts as a flat {name, description} list, in the order norns'
--- own favorites file has them (not re-sorted -- that's what Alphabetize
--- Favorites is for). A rejected script is skipped even if favorited.
local function build_favorites_entries()
  local list = {}
  for _, fav in ipairs(faves) do
    local info = scripts[fav.name]
    if info and not info.rejected then
      table.insert(list, { fav.name, info.description })
    end
  end
  return list
end

--- Every rejected script, alphabetically, regardless of category -- always
--- appended at the very bottom of the full list so they're still findable.
local function build_rejected_entries()
  local list = {}
  for name, info in pairs(scripts) do
    if info.rejected then
      table.insert(list, { name, info.description })
    end
  end
  table.sort(list, function(a, b) return display_name(a[1]):lower() < display_name(b[1]):lower() end)
  return list
end

----------------------------------------------------------------------------
-- Persistence -- categories.json-style data, flattened and sorted for
-- hand-editing: every script keyed by name with a plain category/subcategory
-- string ("" = not yet assigned), and `categories` as a simple ordered taxonomy.
----------------------------------------------------------------------------

local DATA_FILE = 'data.json'

--- A small pretty-printer (sorted keys, indented) instead of lib/json's compact
--- encoder, so the file stays easy to read and hand-edit in a text editor.
local function encode_pretty(val, indent)
  indent = indent or 0
  local pad = string.rep('  ', indent)
  local pad_in = string.rep('  ', indent + 1)

  if type(val) == 'table' then
    if val[1] ~= nil or next(val) == nil then
      if next(val) == nil then return '[]' end
      local parts = {}
      for _, v in ipairs(val) do
        table.insert(parts, pad_in .. encode_pretty(v, indent + 1))
      end
      return '[\n' .. table.concat(parts, ',\n') .. '\n' .. pad .. ']'
    else
      local names = {}
      for k in pairs(val) do table.insert(names, k) end
      table.sort(names)
      local parts = {}
      for _, k in ipairs(names) do
        table.insert(parts, pad_in .. json.encode(k) .. ': ' .. encode_pretty(val[k], indent + 1))
      end
      return '{\n' .. table.concat(parts, ',\n') .. '\n' .. pad .. '}'
    end
  elseif type(val) == 'string' then
    return json.encode(val)
  else
    return tostring(val)
  end
end

local function load_fresh_data()
  local path = norns.state.path .. DATA_FILE

  if util.file_exists(path) then
    local file = io.open(path, 'rb')
    local content = file:read('*all')
    file:close()

    local ok, decoded = pcall(json.decode, content)
    if ok and decoded then
      return decoded.categories or {}, decoded.scripts or {}, decoded.deleted_categories,
        decoded.tutorial_seen or false
    end
  end

  return {}, {}, nil, false
end

local function save_fresh_data()
  local path = norns.state.path .. DATA_FILE
  local file = io.open(path, 'wb')
  if file then
    -- encode_pretty can't tell an empty object from an empty array by shape alone;
    -- categories/scripts are always objects (name -> value), even when empty, so
    -- special-case that rather than risk "categories": [] confusing a hand-editor.
    local cat_text = next(categories) == nil and '{}' or encode_pretty(categories, 1)
    local script_text = next(scripts) == nil and '{}' or encode_pretty(scripts, 1)
    file:write('{\n  "categories": ' .. cat_text .. ',\n  "scripts": ' .. script_text)
    if deleted_categories_backup then
      file:write(',\n  "deleted_categories": ' .. encode_pretty(deleted_categories_backup, 1))
    end
    -- Whether the onboarding tutorial has run its course -- stored here
    -- (not just in the opt_show_tutorial param/pset) because this file's
    -- own read/write has been reliable all session, whereas the pset's
    -- persistence for that param was not: it kept reverting after a
    -- restart, so this is now the real gate at init() time (see there).
    file:write(',\n  "tutorial_seen": ' .. tostring(tutorial_seen))
    file:write('\n}\n')
    file:close()
  end
end

--- Writes the current categories+scripts out to a separate, timestamped file
--- (never read back automatically -- just a manual snapshot), for both the
--- "Backup Organization" function and "Delete all categories"' own backup
--- offer. Returns the filename written.
local function backup_current_data()
  local filename = 'backup_' .. os.date('%y%m%d') .. '.json'
  local path = norns.state.path .. filename
  local file = io.open(path, 'wb')
  if file then
    local cat_text = next(categories) == nil and '{}' or encode_pretty(categories, 1)
    local script_text = next(scripts) == nil and '{}' or encode_pretty(scripts, 1)
    file:write('{\n  "categories": ' .. cat_text .. ',\n  "scripts": ' .. script_text .. '\n}\n')
    file:close()
  end
  return filename
end

--- A bundled, read-only reference catalog (built from norns-community's own
--- script list) used by Auto Sort. Never written to -- only data.json is.
local function load_auto_sorted_catalog()
  local path = norns.state.path .. 'auto_sorted.json'
  if util.file_exists(path) then
    local file = io.open(path, 'rb')
    local content = file:read('*all')
    file:close()
    local ok, decoded = pcall(json.decode, content)
    if ok and decoded then
      return decoded.scripts or {}
    end
  end
  return {}
end

----------------------------------------------------------------------------
-- Category/subcategory taxonomy -- creation, renaming, deletion.
----------------------------------------------------------------------------

local function sorted_category_names()
  local list = {}
  for name in pairs(categories) do table.insert(list, name) end
  table.sort(list, function(a, b) return a:lower() < b:lower() end)
  return list
end

local function sorted_subcategory_names(cat_name)
  local list = {}
  if categories[cat_name] then
    for _, s in ipairs(categories[cat_name]) do table.insert(list, s) end
  end
  table.sort(list, function(a, b) return a:lower() < b:lower() end)
  return list
end

local function name_exists_ci(list, name)
  for _, v in ipairs(list) do
    if v:lower() == name:lower() then return true end
  end
  return false
end

local function clean_name(name)
  return (name or ''):gsub('^%s*(.-)%s*$', '%1')
end

local function category_script_count(cat_name)
  local n = 0
  for _, info in pairs(scripts) do
    if info.category == cat_name then n = n + 1 end
  end
  return n
end

local function subcategory_script_count(cat_name, sub_name)
  local n = 0
  for _, info in pairs(scripts) do
    if info.category == cat_name and info.subcategory == sub_name then n = n + 1 end
  end
  return n
end

local function unsorted_subcategory_count(cat_name)
  local n = 0
  for _, info in pairs(scripts) do
    if info.category == cat_name and (info.subcategory == nil or info.subcategory == '') then
      n = n + 1
    end
  end
  return n
end

-- Forward-declared: defined after build_content_layout's helpers below, but
-- every taxonomy mutation needs to call it, so declare the local up front.
local rebuild_browse_view

local function add_category(name)
  name = clean_name(name)
  if name == '' or name:lower() == 'unsorted' then return false end
  if categories[name] or name_exists_ci(sorted_category_names(), name) then return false end
  categories[name] = {}
  save_fresh_data()
  rebuild_browse_view()
  return true
end

local function rename_category(old, new)
  new = clean_name(new)
  if new == '' or new:lower() == 'unsorted' then return false end
  if new ~= old and name_exists_ci(sorted_category_names(), new) then return false end
  if new == old then return true end

  categories[new] = categories[old]
  categories[old] = nil
  for _, info in pairs(scripts) do
    if info.category == old then info.category = new end
  end
  save_fresh_data()
  rebuild_browse_view()
  return true
end

local function delete_category(name)
  categories[name] = nil
  for _, info in pairs(scripts) do
    if info.category == name then
      info.category = ''
      info.subcategory = ''
    end
  end
  save_fresh_data()
  rebuild_browse_view()
end

local function add_subcategory(cat, name)
  name = clean_name(name)
  if name == '' or name:lower() == 'unsorted' then return false end
  if not categories[cat] then return false end
  if name_exists_ci(categories[cat], name) then return false end
  table.insert(categories[cat], name)
  save_fresh_data()
  rebuild_browse_view()
  return true
end

local function rename_subcategory(cat, old, new)
  new = clean_name(new)
  if new == '' or new:lower() == 'unsorted' then return false end
  if not categories[cat] then return false end
  if new ~= old and name_exists_ci(categories[cat], new) then return false end
  if new == old then return true end

  for i, s in ipairs(categories[cat]) do
    if s == old then categories[cat][i] = new end
  end
  for _, info in pairs(scripts) do
    if info.category == cat and info.subcategory == old then info.subcategory = new end
  end
  save_fresh_data()
  rebuild_browse_view()
  return true
end

local function delete_subcategory(cat, name)
  if categories[cat] then
    for i, s in ipairs(categories[cat]) do
      if s == name then
        table.remove(categories[cat], i)
        break
      end
    end
  end
  for _, info in pairs(scripts) do
    if info.category == cat and info.subcategory == name then info.subcategory = '' end
  end
  save_fresh_data()
  rebuild_browse_view()
end

--- Assigns a category/subcategory to every known script that's still unsorted
--- and appears in the bundled catalog. Never touches a script the user already
--- sorted. Returns { assigned, already, remain } counts.
local function run_auto_sort()
  local catalog = load_auto_sorted_catalog()
  local assigned, already, remain = 0, 0, 0

  for name, info in pairs(scripts) do
    -- A category can go stale (categories deleted/renamed after a script was
    -- sorted into one) without the script's own fields ever being cleared --
    -- rebuild_browse_view already refuses to show those as sorted, so treat
    -- them as not-really-sorted here too, instead of counting them "already"
    -- while they're actually invisible in the real list.
    if info.category ~= '' and not categories[info.category] then
      info.category = ''
      info.subcategory = ''
    end

    if info.category ~= '' then
      already = already + 1
    else
      local entry = catalog[name]
      if entry and categories[entry.category] then
        info.category = entry.category
        info.subcategory = entry.subcategory or ''
        assigned = assigned + 1
      else
        remain = remain + 1
      end
    end
  end

  save_fresh_data()
  rebuild_browse_view()
  return { assigned = assigned, already = already, remain = remain }
end

--- Clears every script's category/subcategory (not its rejected tag --
--- rejection and sorting are separate concepts).
local function reset_sorting()
  for _, info in pairs(scripts) do
    info.category = ''
    info.subcategory = ''
  end
  save_fresh_data()
  rebuild_browse_view()
end

local REPLACE_HOME_NBSP = '\194\160'

--- True for a favorite that `perform_replace_home` put there: freshlook
--- itself (identified by path, not name -- freshlook is never renamed) or
--- one of its blank spacers (identified by a name that's nothing but NBSPs,
--- which nothing else would ever legitimately be named).
local function is_replace_home_pinned(fav)
  if fav.path == norns.state.path then return true end
  return fav.name ~= '' and fav.name:gsub(REPLACE_HOME_NBSP, '') == ''
end

--- Sorts favorites alphabetically, except freshlook itself and its blank
--- spacers (see `is_replace_home_pinned`) -- those stay pinned at the top,
--- in whatever order they're already in, instead of getting scrambled in.
local function alphabetize_favorites()
  local pinned, rest = {}, {}
  for _, fav in ipairs(faves) do
    if is_replace_home_pinned(fav) then
      table.insert(pinned, fav)
    else
      table.insert(rest, fav)
    end
  end
  table.sort(rest, function(a, b) return a.name:lower() < b.name:lower() end)
  faves = pinned
  for _, fav in ipairs(rest) do table.insert(faves, fav) end
  tabutil.save(faves, _path.favorites)
end

local REPLACE_HOME_BLANK_COUNT = 10

--- Favorites freshlook (wherever it already lives -- never renamed or
--- moved) at the very top, with `REPLACE_HOME_BLANK_COUNT` blank/invisible
--- scripts favorited right behind it, so the favorites screen (norns' own
--- home/boot screen) shows nothing else until you scroll. Pure favorites +
--- data-file work, no renaming anything that's currently running, so
--- there's nothing here that can corrupt this session's own state. Safe to
--- run more than once: each blank is only (re)created if it doesn't
--- already exist.
local function perform_replace_home()
  local base = _path.code
  local current_name = norns.state.path:sub(1, -2):match('([^/]+)$')
  local current_file = norns.state.path .. current_name .. '.lua'

  local new_faves = {}
  for i = 1, REPLACE_HOME_BLANK_COUNT do
    local blank_name = REPLACE_HOME_NBSP:rep(i)
    local dir = base .. blank_name .. '/'
    if not util.file_exists(dir) then
      os.execute(string.format("mkdir -p '%s'", dir))
      local file = io.open(dir .. blank_name .. '.lua', 'wb')
      if file then
        file:write('-- ------------------------------------------\n-- blank\n')
        file:close()
      end
    end
    if not scripts[blank_name] then
      scripts[blank_name] = { description = '', category = '', subcategory = '', rejected = true }
    end
    table.insert(new_faves, favorite_entry(blank_name, dir .. blank_name .. '.lua'))
  end

  if not scripts[current_name] then
    scripts[current_name] = { description = '', category = '', subcategory = '', rejected = false }
  end
  scripts[current_name].rejected = true

  save_fresh_data()
  rebuild_browse_view()

  -- Favorite freshlook (first) and the blanks (right after) -- replacing
  -- any pre-existing favorite entries for these exact ones rather than
  -- duplicating them, since this can run more than once.
  local kept = {}
  for _, fav in ipairs(faves) do
    if not is_replace_home_pinned(fav) then table.insert(kept, fav) end
  end
  faves = { favorite_entry(current_name, current_file) }
  for _, fav in ipairs(new_faves) do table.insert(faves, fav) end
  for _, fav in ipairs(kept) do table.insert(faves, fav) end
  tabutil.save(faves, _path.favorites)
end

----------------------------------------------------------------------------
-- Derive the browse view from categories + scripts.
----------------------------------------------------------------------------

rebuild_browse_view = function()
  -- Pre-seed every defined category/subcategory, even empty ones, so a
  -- freshly-created category/subcategory is immediately browsable (0 total).
  local groups = {}
  for cat_name, subs in pairs(categories) do
    groups[cat_name] = groups[cat_name] or {}
    for _, sub_name in ipairs(subs) do
      groups[cat_name][sub_name] = groups[cat_name][sub_name] or {}
    end
  end

  local unsorted_flat = {}

  for name, info in pairs(scripts) do
    -- A category can go stale (deleted/renamed after a script was sorted into
    -- it) without the script's own fields ever being cleared -- fix that up
    -- here too, not just right after Auto Sort, so the Sort Scripts list's
    -- "already sorted" filter (which just checks non-empty) can't disagree
    -- with what the browse view actually shows.
    if info.category ~= '' and not categories[info.category] then
      info.category = ''
      info.subcategory = ''
    end

    if not info.rejected then
      local cat = info.category
      if cat == nil or cat == '' or not categories[cat] then
        table.insert(unsorted_flat, { name, info.description })
      else
        local sub = info.subcategory
        if sub == nil or sub == '' then sub = 'Unsorted' end
        groups[cat] = groups[cat] or {}
        groups[cat][sub] = groups[cat][sub] or {}
        table.insert(groups[cat][sub], { name, info.description })
      end
    end
  end

  data = {}
  keys = {}

  for cat_name, subs in pairs(groups) do
    if subs['Unsorted'] and #subs['Unsorted'] == 0 then
      subs['Unsorted'] = nil
    end
    data[cat_name] = subs
    table.insert(keys, cat_name)
  end

  if #unsorted_flat > 0 then
    data['Unsorted'] = unsorted_flat
    table.insert(keys, 'Unsorted')
  end

  table.sort(keys, function(a, b)
    local a_u = a:lower() == 'unsorted'
    local b_u = b:lower() == 'unsorted'
    if a_u ~= b_u then return b_u end
    return a:lower() < b:lower()
  end)

  -- Alphabetize entries within every (sub)category, and re-tag/float favorites.
  local favorite_names = {}
  for _, fav in pairs(faves) do favorite_names[fav.name] = true end
  local reorder = opt_on('opt_favorites_at_top')

  local function by_display_name(a, b)
    return display_name(a[1]):lower() < display_name(b[1]):lower()
  end

  for _, cat_name in ipairs(keys) do
    if is_subcategory_map(data[cat_name]) then
      for sub_name, list in pairs(data[cat_name]) do
        table.sort(list, by_display_name)
        data[cat_name][sub_name] = float_favorites(list, favorite_names, reorder)
      end
    else
      table.sort(data[cat_name], by_display_name)
      data[cat_name] = float_favorites(data[cat_name], favorite_names, reorder)
    end
  end
end

----------------------------------------------------------------------------
-- Browse: content layout -- turns `data` (built above) into the flat,
-- row-by-row `layout` that redraw_browse actually walks to draw the
-- screen and scroll through it.
----------------------------------------------------------------------------

local function make_card_item(entry)
  return { kind = 'card', details = entry, height = card_height }
end

--- Build the row-by-row content layout. A (sub)category can be entirely
--- empty (freshly created, nothing sorted into it yet), so the leading
--- blank row always anchors index_map -- not just the first real entry --
--- or an empty category would crash category_rows below.
local function build_content_layout()
  local layout = {}
  local index_map = {}
  local first_entry_positions = {}
  local full_view = is_full_view()

  -- The full list's own content (both Compact and Expanded) always skips
  -- empty (sub)categories outright -- there's nothing to scroll to there,
  -- just dead blank space with the header changing for no reason. Expanded
  -- additionally *requires* this: it pages cards at a fixed stride, and a
  -- header with zero cards behind it breaks that stride and scrambles every
  -- card_index calculation after it. "Hide Empty Categories" only affects
  -- what Quick Nav lists, never the full list itself.
  local vk = nonempty_keys()

  for i, k in ipairs(vk) do
    local category_anchored = false

    if full_view then
      table.insert(layout, { kind = 'header', x = 1, label = k })
      index_map[k] = #layout
      category_anchored = true
    end

    if is_subcategory_map(data[k]) then
      for _, sk in ipairs(nonempty_subkeys(data[k])) do
        local sub_anchored = false

        if not full_view then
          table.insert(layout, { kind = 'blank' })
          index_map[k .. '\0' .. sk] = #layout
          sub_anchored = true
          if not category_anchored then
            index_map[k] = #layout
            category_anchored = true
          end
        end

        for j = 1, #data[k][sk] do
          local entry = data[k][sk][j]
          if full_view then
            table.insert(layout, make_card_item(entry))
          else
            table.insert(layout, { kind = 'entry', x = entry_x, details = entry })
          end

          if not category_anchored then
            index_map[k] = #layout
            category_anchored = true
          end
          if not sub_anchored then
            index_map[k .. '\0' .. sk] = #layout
            sub_anchored = true
          end
          if j == 1 then table.insert(first_entry_positions, #layout) end
        end

        if not full_view then
          table.insert(layout, { kind = 'blank' })
        end
      end
    else
      if not full_view then
        table.insert(layout, { kind = 'blank' })
        if not category_anchored then
          index_map[k] = #layout
          category_anchored = true
        end
      end

      for j = 1, #data[k] do
        local entry = data[k][j]
        if full_view then
          table.insert(layout, make_card_item(entry))
        else
          table.insert(layout, { kind = 'entry', x = entry_x, details = entry })
        end

        if not category_anchored then
          index_map[k] = #layout
          category_anchored = true
        end
        if j == 1 then table.insert(first_entry_positions, #layout) end
      end

      if not full_view then
        table.insert(layout, { kind = 'blank' })
      end
    end

    if full_view and i < #vk then
      table.insert(layout, { kind = 'separator' })
    end
  end

  return layout, index_map, first_entry_positions
end

local function build_nav_layout(index_map)
  local nav = {}

  for _, k in ipairs(visible_keys()) do
    table.insert(nav, {
      kind = 'nav',
      x = 1,
      label = titlecase(k),
      fav = count_favorites(data[k]),
      total = count_entries(data[k]),
      content_pos = index_map[k],
    })

    if is_subcategory_map(data[k]) then
      for _, sk in ipairs(visible_subkeys(data[k])) do
        table.insert(nav, {
          kind = 'nav',
          x = 8,
          label = titlecase(sk),
          fav = count_favorites(data[k][sk]),
          total = #data[k][sk],
          content_pos = index_map[k .. '\0' .. sk],
        })
      end
    end
  end

  return nav
end

local function compute_rows(layout)
  local rows = {}
  local cumulative = 0
  for i, item in ipairs(layout) do
    rows[i] = cumulative + 2
    cumulative = cumulative + (item.height or 1)
  end
  return rows, cumulative
end

local function build_layout()
  local content, index_map, first_entry_positions = build_content_layout()
  local nav = build_nav_layout(index_map)
  local full_view = is_full_view()

  local favorites_entries = build_favorites_entries()
  local show_before = opt_on('opt_favorites_before_full')
  local quick_nav_on = opt_on('opt_show_quick_nav')
  local show_folder = quick_nav_on and opt_on('opt_favorites_folder_nav')

  --- The favorites section's own rows, with NO marker/separator framing --
  --- Expanded can't have a non-card row inside its paged zone without
  --- breaking the fixed card_height stride every card_index calculation
  --- depends on. Framing (in Compact only) is added by the caller instead.
  local function favorites_block()
    local items = {}
    for _, e in ipairs(favorites_entries) do
      if full_view then
        table.insert(items, make_card_item(e))
      else
        table.insert(items, { kind = 'entry', x = entry_x, details = e })
      end
    end
    return items
  end

  local favorites_nav_item = nil
  if show_folder then
    favorites_nav_item = { kind = 'nav', x = 1, label = '*Favorites', fav = 0, total = #favorites_entries }
  end

  -- Mirrors `content`, but with favorites cards woven in at the same position
  -- they're woven into `layout` below -- Expanded's card_index indexes into
  -- this, not raw `content`, whenever favorites are shown as their own block.
  local indexable_content = content

  local layout = {}

  -- The very first thing anyone sees, unless "Show Instructions" is off --
  -- and where repeated K2 "back" presses eventually land, since pos 0 always
  -- starts here now. Condensed to exactly 5 rows (K2/K3 sharing a line, no
  -- blank before the scroll cue) because the first row at pos 0 always lands
  -- one row below the very top of the screen -- any more than 5 and "vvv
  -- scroll vvv" itself would scroll out of view on the opening screen.
  if opt_on('opt_show_instructions') then
    for _, line in ipairs({
      'E2 - scroll categories',
      'E3 - scroll',
      'K1 long - settings',
      'K2 back        K3 load',
    }) do
      table.insert(layout, { kind = 'hint', label = line })
    end
    table.insert(layout, { kind = 'hint', label = 'vvv scroll vvv', bright = true })
  end

  -- Row where the opening instructions end and the real content (Quick Nav or
  -- the full list) begins -- the frozen header bar stays off entirely until
  -- you've scrolled past this, rather than labeling the instructions screen
  -- itself "Quick Nav".
  local instructions_len = #layout

  if quick_nav_on then
    local full_after_nav = opt_on('opt_show_full_after_nav')

    for _, name in ipairs(pinned_scripts) do
      local e = find_entry(name)
      if e then
        table.insert(layout, { kind = 'pinned', details = e })
      end
    end
    table.insert(layout, { kind = 'blank' })
    if opt_on('opt_show_quick_nav_count') then
      table.insert(layout, { kind = 'nav_columns' })
    end
    if favorites_nav_item then table.insert(layout, favorites_nav_item) end
    for _, item in ipairs(nav) do table.insert(layout, item) end
    table.insert(layout, { kind = 'blank' })

    -- Favorites-before takes over the "FULL LIST" transition's job -- it IS
    -- the signal that Quick Nav has ended, so showing both would be redundant.
    if not show_before then
      if full_after_nav then
        table.insert(layout, { kind = 'separator' })
        table.insert(layout, { kind = 'marker', label = 'FULL LIST' })
        table.insert(layout, { kind = 'separator' })
      else
        -- Second buffer blank: keeps the full list's first real row from peeking
        -- onto the bottom of the screen when centered on the very last nav row
        -- (see the cap math in enc_browse, tuned for exactly this structure).
        table.insert(layout, { kind = 'blank' })
      end
    end
  else
    -- Quick Nav off: the full list is all there is, so it gets its own title
    -- instead of starting with no context at all -- unless favorites-before
    -- is taking that slot instead.
    if not show_before then
      table.insert(layout, { kind = 'separator' })
      table.insert(layout, { kind = 'marker', label = 'Full List' })
      table.insert(layout, { kind = 'separator' })
    end
  end

  -- Everything from here on is the pageable zone (Expanded's card_index
  -- starts counting from prefix_len+1), so favorites-before has to be
  -- inserted AFTER this capture, not before.
  local prefix_len = #layout
  local favorites_span_start_pos, favorites_span_end_pos = nil, nil

  if show_before then
    favorites_span_start_pos = #layout + 1
    if full_view then
      local items = favorites_block()
      if favorites_nav_item then favorites_nav_item.direct_pos = #layout + 1 end
      for _, it in ipairs(items) do table.insert(layout, it) end
      indexable_content = {}
      for _, it in ipairs(items) do table.insert(indexable_content, it) end
      for _, it in ipairs(content) do table.insert(indexable_content, it) end
    else
      table.insert(layout, { kind = 'marker', label = 'FAVORITES' })
      if favorites_nav_item then favorites_nav_item.direct_pos = #layout end
      table.insert(layout, { kind = 'separator' })
      table.insert(layout, { kind = 'blank' })
      for _, it in ipairs(favorites_block()) do table.insert(layout, it) end
      table.insert(layout, { kind = 'blank' })
      table.insert(layout, { kind = 'separator' })
    end
    favorites_span_end_pos = #layout
  end

  -- When favorites-before pushed content later in `layout` than `prefix_len`,
  -- every index_map lookup (which is relative to `content` itself) needs this
  -- added on top of prefix_len to land on the right row.
  local content_offset = #layout - prefix_len
  for _, item in ipairs(content) do table.insert(layout, item) end

  if show_folder and not show_before then
    favorites_span_start_pos = #layout + 1
    if full_view then
      local items = favorites_block()
      if favorites_nav_item then favorites_nav_item.direct_pos = #layout + 1 end
      indexable_content = {}
      for _, it in ipairs(content) do table.insert(indexable_content, it) end
      for _, it in ipairs(items) do table.insert(indexable_content, it) end
      for _, it in ipairs(items) do table.insert(layout, it) end
    else
      table.insert(layout, { kind = 'blank' })
      table.insert(layout, { kind = 'separator' })
      table.insert(layout, { kind = 'marker', label = 'FAVORITES' })
      if favorites_nav_item then favorites_nav_item.direct_pos = #layout end
      table.insert(layout, { kind = 'separator' })
      table.insert(layout, { kind = 'blank' })
      for _, it in ipairs(favorites_block()) do table.insert(layout, it) end
    end
    favorites_span_end_pos = #layout
  end

  -- Rejected scripts, regardless of category: always appended at the very
  -- bottom (after a bottom-placed favorites block, if any) so they're still
  -- findable/launchable, never grouped by whatever they used to be sorted as.
  local rejected_entries = build_rejected_entries()
  local rejected_span_start_pos, rejected_span_end_pos = nil, nil

  if #rejected_entries > 0 then
    rejected_span_start_pos = #layout + 1
    if full_view then
      local items = {}
      for _, e in ipairs(rejected_entries) do table.insert(items, make_card_item(e)) end
      for _, it in ipairs(items) do table.insert(indexable_content, it) end
      for _, it in ipairs(items) do table.insert(layout, it) end
    else
      table.insert(layout, { kind = 'blank' })
      table.insert(layout, { kind = 'separator' })
      table.insert(layout, { kind = 'marker', label = 'REJECTED' })
      table.insert(layout, { kind = 'separator' })
      table.insert(layout, { kind = 'blank' })
      for _, e in ipairs(rejected_entries) do
        table.insert(layout, { kind = 'entry', x = entry_x, details = e })
      end
    end
    rejected_span_end_pos = #layout
  end

  local rows, total_rows = compute_rows(layout)

  for _, item in ipairs(layout) do
    if item.kind == 'nav' then
      if item.direct_pos then
        item.target_row = rows[item.direct_pos]
      else
        -- With "Hide Empty Categories" off, Quick Nav can list a (sub)category
        -- that the full list itself always omits (nothing to scroll to there),
        -- so it has no anchor in index_map/content_pos at all -- leave
        -- target_row nil rather than crash; selecting it is just a no-op.
        item.target_row = item.content_pos and rows[prefix_len + content_offset + item.content_pos] or nil
      end
    end
  end

  local stops = { 2 }
  for i, item in ipairs(layout) do
    if (item.kind == 'nav' and item.x == 1)
      or (item.kind == 'marker' and item.label ~= 'REJECTED') then
      table.insert(stops, rows[i])
    end
  end
  for _, pos in ipairs(first_entry_positions) do
    table.insert(stops, rows[prefix_len + content_offset + pos])
  end

  -- A bottom-placed favorites section's own marker row gets collected in the
  -- first loop (by layout position, near the end) before first_entry_positions'
  -- rows are appended (all within `content`, i.e. earlier) -- leaving `stops`
  -- out of ascending order, which made E2 oscillate near the end instead of
  -- just clamping. jump_section's forward/backward scan assumes ascending order.
  table.sort(stops)

  local max_pos = total_rows - 2

  -- These mirror the full list's own content (always non-empty), not Quick
  -- Nav's -- index_map only has anchors for what content actually included,
  -- and with "Hide Empty Categories" off, Quick Nav can list more than that.
  local category_rows = {}
  for _, k in ipairs(nonempty_keys()) do
    table.insert(category_rows, { name = k, row = rows[prefix_len + content_offset + index_map[k]] })
  end

  local subcategory_rows = {}
  for _, k in ipairs(nonempty_keys()) do
    if is_subcategory_map(data[k]) then
      for _, sk in ipairs(nonempty_subkeys(data[k])) do
        table.insert(subcategory_rows, {
          category = k,
          name = sk,
          row = rows[prefix_len + content_offset + index_map[k .. '\0' .. sk]],
        })
      end
    end
  end

  -- Only meaningful when Quick Nav is actually showing -- when it's off, the
  -- instructions are immediately followed by the "Full List" title, not Quick
  -- Nav content, so there's no "Quick Nav" window to frame at all.
  local quick_nav_start = quick_nav_on
    and (rows[instructions_len + 1] or (instructions_len + 2))
    or nil

  local favorites_row_span = favorites_span_start_pos
    and { rows[favorites_span_start_pos], rows[favorites_span_end_pos] }
    or nil

  local rejected_row_span = rejected_span_start_pos
    and { rows[rejected_span_start_pos], rows[rejected_span_end_pos] }
    or nil

  return layout, stops, max_pos, category_rows, subcategory_rows,
    rows[prefix_len + 1] or (prefix_len + 2), indexable_content, prefix_len,
    quick_nav_start, favorites_row_span, rejected_row_span
end

local function category_at_row(row, category_rows)
  local current = nil
  for _, c in ipairs(category_rows) do
    if c.row <= row then
      current = c.name
    else
      break
    end
  end
  return current
end

local function subcategory_at_row(row, category_name, subcategory_rows)
  local current = nil
  for _, s in ipairs(subcategory_rows) do
    if s.row > row then
      break
    end
    if s.category == category_name then
      current = s.name
    end
  end
  return current
end

local function jump_section(delta)
  local _, stops, max_pos, _, _, full_list_start = build_layout()
  max_pos = math.max(0, max_pos) -- never let a degenerate (near-empty) list invert the clamp bounds
  local current_row = params:get('pos') + 3
  if #stops == 0 then return end

  if opt_on('opt_show_quick_nav') and not opt_on('opt_show_full_after_nav')
      and current_row < full_list_start then
    local filtered = {}
    for _, row in ipairs(stops) do
      if row < full_list_start then table.insert(filtered, row) end
    end
    stops = filtered
    if #stops == 0 then return end
  end

  if delta > 0 then
    for _, row in ipairs(stops) do
      if row > current_row then
        params:set('pos', util.clamp(row - 3, 0, max_pos))
        return
      end
    end
    params:set('pos', util.clamp(stops[#stops] - 3, 0, max_pos))
  else
    for i = #stops, 1, -1 do
      if stops[i] < current_row then
        params:set('pos', util.clamp(stops[i] - 3, 0, max_pos))
        return
      end
    end
    params:set('pos', util.clamp(stops[1] - 3, 0, max_pos))
  end
end

--- Splits `line` into alternating { text, hl } segments around every
--- case-insensitive occurrence of `needle`, preserving everything else
--- (including spacing) exactly as-is.
local function split_highlight(line, needle)
  local segments = {}
  local lower_line, lower_needle = line:lower(), needle:lower()
  local pos = 1
  while true do
    local s, e = lower_line:find(lower_needle, pos, true)
    if not s then
      table.insert(segments, { text = line:sub(pos), hl = false })
      break
    end
    if s > pos then
      table.insert(segments, { text = line:sub(pos, s - 1), hl = false })
    end
    table.insert(segments, { text = line:sub(s, e), hl = true })
    pos = e + 1
  end
  return segments
end

--- screen.text_extents() trims leading/trailing whitespace out of its own
--- width, so chaining it across segments was eating the space around a
--- highlighted word. This adds it back in by measuring the non-space core
--- and the edge spaces separately.
local function segment_width(text)
  if text == '' then return 0 end
  local core = text:match('^%s*(.-)%s*$')
  local edge_spaces = #text - #core
  local core_w = core ~= '' and screen.text_extents(core) or 0
  return core_w + space_width * edge_spaces
end

--- Draws `line` (horizontally centered, unless `align == 'left'`), same as
--- screen.text_center, except every "freshlook" in it renders at full
--- brightness while everything else is noticeably dimmer -- used by the
--- tutorial/guide screens so the app's own name stands out.
local function draw_line_with_freshlook_highlighted(y, line, align)
  local segments = split_highlight(line, 'freshlook')
  local x
  if align == 'left' then
    x = 1
  else
    local total_w = 0
    for _, seg in ipairs(segments) do total_w = total_w + segment_width(seg.text) end
    x = 64 - total_w / 2
  end
  for _, seg in ipairs(segments) do
    screen.level(seg.hl and 15 or 7)
    screen.move(x, y)
    screen.text(seg.text)
    x = x + segment_width(seg.text)
  end
end

--- Shared by Compact/Expanded's per-row `draw_selectable` closure and Linear
--- view's script list -- identical look: '* ' favorite prefix, description
--- column when "Show Descriptions" is on, dim unless `highlighted`.
local function draw_script_row(x, y, label, desc, is_fav, highlighted, on_select)
  if highlighted then
    screen.level(15)
    if on_select then on_select() end
  else
    screen.level(2)
  end

  local show_desc = opt_on('opt_show_descriptions')

  screen.move(x, y)
  local text = label
  local text_len = show_desc and (type_size * 1.25) or (type_size * 3)
  if is_fav then
    text = '* ' .. text
    text_len = text_len + 2
  end
  text_trunc(text, text_len)

  if show_desc and desc ~= nil then
    screen.move(desc_x, y)
    text_trunc(desc, type_size * 1.5)
  end
end

----------------------------------------------------------------------------
-- Linear view mode: category -> subcategory -> scripts, menu-dive style.
----------------------------------------------------------------------------

local function linear_reset()
  linear_step = 1
  linear_pos = 1
  linear_category = nil
  linear_subcategory = nil
end

--- The current level's selectable rows: { name, total, fav } for a category
--- or subcategory row, { entry = {name, desc, is_fav} } for a script row.
--- Categories/subcategories use `visible_keys`/`visible_subkeys` (not the
--- always-nonempty variants) so "Hide Empty Categories" governs Linear the
--- same way it governs Quick Nav.
local function linear_rows()
  local rows = {}
  if linear_step == 1 then
    for _, k in ipairs(visible_keys()) do
      table.insert(rows, { name = k, total = count_entries(data[k]), fav = count_favorites(data[k]) })
    end
  elseif linear_step == 2 then
    local node = data[linear_category]
    for _, sk in ipairs(visible_subkeys(node)) do
      table.insert(rows, { name = sk, total = count_entries(node[sk]), fav = count_favorites(node[sk]) })
    end
  else
    local node = linear_subcategory and data[linear_category][linear_subcategory] or data[linear_category]
    for _, e in ipairs(node) do
      table.insert(rows, { entry = e })
    end
  end
  return rows
end

local LINEAR_LIST_TOP = 24
local LINEAR_VISIBLE_ROWS = 4

local function redraw_linear()
  -- Horizontal progress bar across the top, split into thirds -- one lit
  -- per step, so it's always visible which level you're at.
  screen.level(2)
  screen.move(0, 1)
  screen.line(127, 1)
  screen.stroke()
  local seg = 127 / 3
  screen.level(15)
  local x0 = (linear_step - 1) * seg
  screen.move(x0, 1)
  screen.line(x0 + seg, 1)
  screen.stroke()

  -- Omnipresent title bar.
  screen.level(4)
  screen.move(1, 11)
  if linear_step == 1 then
    screen.text('Category:')
  elseif linear_step == 2 then
    text_trunc(titlecase(linear_category), 13)
    screen.move(127, 11)
    screen.text_right('sub-category:')
  else
    text_trunc(titlecase(linear_category), 13)
    if linear_subcategory then
      screen.move(127, 11)
      screen.text_right(titlecase(linear_subcategory))
    end
  end

  local rows = linear_rows()
  if #rows == 0 then return end
  linear_pos = util.clamp(linear_pos, 1, #rows)

  -- Scrolls just enough to keep linear_pos in view, as the last visible row
  -- once the list overflows -- never negative, never past the final page.
  local max_offset = math.max(0, #rows - LINEAR_VISIBLE_ROWS)
  local offset = util.clamp(linear_pos - LINEAR_VISIBLE_ROWS, 0, max_offset)

  local y = LINEAR_LIST_TOP
  for i = offset + 1, math.min(#rows, offset + LINEAR_VISIBLE_ROWS) do
    local row = rows[i]
    local highlighted = (i == linear_pos)
    if row.entry then
      draw_script_row(1, y, display_name(row.entry[1]), row.entry[2], row.entry[3], highlighted, function()
        selection = { kind = 'script', name = row.entry[1], desc = row.entry[2] }
      end)
    else
      if highlighted then screen.level(15) else screen.level(2) end
      screen.move(1, y)
      text_trunc(titlecase(row.name), nav_label_len)
      if opt_on('opt_show_quick_nav_count') then
        screen.move(nav_fav_x, y)
        screen.text(tostring(row.fav))
        screen.move(nav_total_x, y)
        screen.text_right(tostring(row.total))
      elseif row.total == 0 and not opt_on('opt_hide_empty') then
        screen.move(nav_total_x, y)
        screen.text_right('[empty]')
      end
    end
    y = y + line_height
  end
end

local function enc_linear(index, delta)
  if index == 3 then
    local rows = linear_rows()
    linear_pos = util.clamp(linear_pos + delta, 1, math.max(1, #rows))
  elseif index == 1 and linear_step == 3 and selection ~= nil and selection.kind == 'script' then
    local now = util.time()
    if now - last_favorite_time >= 1 then
      if delta > 0 then
        add_favorite(selection.name)
      else
        remove_favorite(selection.name)
      end
      rebuild_browse_view()
      last_favorite_time = now
    end
  end
end

local function key_linear(index, state)
  if index == 3 then
    local rows = linear_rows()
    local row = rows[linear_pos]
    if not row then return end

    if linear_step == 1 then
      linear_category = row.name
      linear_pos = 1
      linear_step = is_subcategory_map(data[row.name]) and 2 or 3
      if linear_step == 3 then linear_subcategory = nil end
    elseif linear_step == 2 then
      linear_subcategory = row.name
      linear_step = 3
      linear_pos = 1
    else
      selection = { kind = 'script', name = row.entry[1], desc = row.entry[2] }
      if opt_on('opt_show_script_info') then
        browse_confirm = true
      else
        local file, reason = resolve_script_file(selection.name)
        if file then
          norns.script.load(file)
        else
          show_message(reason)
        end
      end
    end
  elseif index == 2 then
    if linear_step == 3 then
      linear_step = linear_subcategory and 2 or 1
      linear_pos = 1
    elseif linear_step == 2 then
      linear_step = 1
      linear_pos = 1
    end
  end
end

----------------------------------------------------------------------------
-- Browse: enc/key/redraw -- the main scrolling list view (Compact/Expanded)
-- that most of the app's time is spent in.
----------------------------------------------------------------------------

local function enc_browse(index, delta)
  if browse_confirm then return end
  if params:get('opt_view_mode') == 3 then
    enc_linear(index, delta)
    return
  end
  if index == 3 then
    local _, _, max_pos, _, _, full_list_start = build_layout()
    max_pos = math.max(0, max_pos)
    local current_row = params:get('pos') + 3
    local step = delta
    if is_full_view() and current_row >= full_list_start then
      step = delta * card_height
    end

    local new_pos = params:get('pos') + step

    if opt_on('opt_show_quick_nav') and not opt_on('opt_show_full_after_nav') then
      -- full_list_start - 6 can go negative when Quick Nav's own section is
      -- short (e.g. instructions hidden, only "Unsorted" shown) -- clamping
      -- it to 0 keeps the cap active instead of silently no-opping (pos=0
      -- is never <= a negative cap_pos, so the min() below never ran).
      local cap_pos = math.max(0, full_list_start - 6)
      if params:get('pos') <= cap_pos then
        new_pos = math.min(new_pos, cap_pos)
      end
    end

    params:set('pos', util.clamp(new_pos, 0, max_pos))
  elseif index == 1 and selection ~= nil and selection.kind == 'script' then
    local now = util.time()
    if now - last_favorite_time >= 1 then
      if delta > 0 then
        add_favorite(selection.name)
      else
        remove_favorite(selection.name)
      end
      rebuild_browse_view()
      last_favorite_time = now
    end
  elseif index == 2 then
    jump_section(delta)
  end
end

local function key_browse(index, state)
  if browse_confirm then
    if index == 3 and selection then
      browse_confirm = false
      local file, reason = resolve_script_file(selection.name)
      if file then
        norns.script.load(file)
      else
        show_message(reason)
      end
    end
    return
  end

  if params:get('opt_view_mode') == 3 then
    key_linear(index, state)
    return
  end

  if index == 3 and selection ~= nil then
    if selection.kind == 'nav' then
      if selection.target_row then
        local _, _, max_pos = build_layout()
        max_pos = math.max(0, max_pos)
        nav_back_pos = params:get('pos')
        params:set('pos', util.clamp(selection.target_row - 3, 0, max_pos))
      end
    elseif opt_on('opt_show_script_info') then
      browse_confirm = true
    else
      local file, reason = resolve_script_file(selection.name)
      if file then
        norns.script.load(file)
      else
        show_message(reason)
      end
    end
  end
end

local function redraw_browse()
  if browse_confirm and selection then
    screen.level(15)
    screen.move(1, 14)
    text_trunc(display_name(selection.name), 21)
    screen.level(4)
    local y = 14 + line_height
    for _, line in ipairs(wrap_text(selection.desc or '', full_desc_wrap_chars)) do
      if y > 14 + (line_height * 3) then break end
      screen.move(1, y)
      screen.text(line)
      y = y + line_height
    end
    screen.level(2)
    screen.move(64, 58)
    screen.text_center('K2 back        K3 load')
    return
  end

  if params:get('opt_view_mode') == 3 then
    redraw_linear()
    return
  end

  local index = 2
  local pos = -params:get('pos')

  local function next_y(rows)
    local y = (pos * line_height) + (line_height * index)
    index = index + (rows or 1)
    return y
  end

  local function draw_separator(y)
    screen.level(2)
    screen.move(0, y)
    screen.line(127, y)
    screen.stroke()
  end

  local function draw_hint(y, text, bright)
    screen.level(bright and 15 or 2)
    if bright then
      screen.move(64, y)
      screen.text_center(text)
    else
      screen.move(1, y)
      screen.text(text)
    end
  end

  local function draw_marker(y, text)
    screen.level(y == (line_height * 3) and 15 or 4)
    screen.move(64, y)
    screen.text_center(text)
  end

  local function draw_nav_columns(y)
    screen.level(2)
    screen.move(nav_fav_x, y)
    screen.text('Fav')
    screen.move(nav_total_x, y)
    screen.text_right('#')
  end

  local function draw_selectable(x, y, label, desc, is_fav, on_select)
    draw_script_row(x, y, label, desc, is_fav, y == (line_height * 3), on_select)
  end

  local function draw_nav_row(x, y, label, fav, total, on_select)
    if y == (line_height * 3) then
      screen.level(15)
      on_select()
    else
      screen.level(2)
    end

    screen.move(x, y)
    text_trunc(label, nav_label_len)

    if opt_on('opt_show_quick_nav_count') then
      screen.move(nav_fav_x, y)
      screen.text(tostring(fav))

      screen.move(nav_total_x, y)
      screen.text_right(tostring(total))
    elseif total == 0 and not opt_on('opt_hide_empty') then
      -- With counts off, an empty (sub)category looks identical to a normal
      -- one -- clicking in just lands on dead space. This at least warns you
      -- first, since that combination is exactly what leaves empty ones visible.
      screen.move(nav_total_x, y)
      screen.text_right('[empty]')
    end
  end

  local function draw_full_page(card)
    selection = { kind = 'script', name = card.details[1], desc = card.details[2] }

    local title_lines = wrap_text(display_name(card.details[1]), full_title_wrap_chars)
    local show_desc = opt_on('opt_show_descriptions')

    local ty = 20
    screen.level(15)
    screen.aa(1)
    screen.font_size(full_title_font)
    local title_prefix = card.details[3] and '* ' or ''
    for li, line in ipairs(title_lines) do
      screen.move(1, ty)
      screen.text((li == 1) and (title_prefix .. line) or line)
      if li < #title_lines then
        ty = ty + full_title_line_height
      end
    end
    screen.font_size(type_size)
    screen.aa(0)

    ty = ty + 6

    if show_desc then
      screen.level(2)
      screen.move(1, ty)
      screen.line(127, ty)
      screen.stroke()
      ty = ty + line_height

      for _, line in ipairs(wrap_text(card.details[2], full_desc_wrap_chars)) do
        if ty > 63 then break end
        screen.move(1, ty)
        screen.text(line)
        ty = ty + line_height
      end
    end
  end

  local layout, _, max_pos, category_rows, subcategory_rows, full_list_start, content, _, quick_nav_start, favorites_row_span, rejected_row_span = build_layout()

  for _, item in ipairs(layout) do
    local y = next_y(item.height)

    if item.kind == 'separator' then
      draw_separator(y)
    elseif item.kind == 'hint' then
      draw_hint(y, item.label, item.bright)
    elseif item.kind == 'marker' then
      draw_marker(y, item.label)
    elseif item.kind == 'nav_columns' then
      draw_nav_columns(y)
    elseif item.kind == 'entry' then
      draw_selectable(item.x, y, display_name(item.details[1]), item.details[2], item.details[3], function()
        selection = { kind = 'script', name = item.details[1], desc = item.details[2] }
      end)
    elseif item.kind == 'pinned' then
      draw_selectable(1, y, '> ' .. display_name(item.details[1]), item.details[2], false, function()
        selection = { kind = 'script', name = item.details[1], desc = item.details[2] }
      end)
    elseif item.kind == 'nav' then
      draw_nav_row(item.x, y, item.label, item.fav, item.total, function()
        selection = { kind = 'nav', target_row = item.target_row }
      end)
    end
  end

  local current_row = params:get('pos') + 3

  if is_full_view() and current_row >= full_list_start then
    local card_index = math.floor((current_row - full_list_start) / card_height) + 1
    card_index = util.clamp(card_index, 1, #content)
    local card = content[card_index]
    if card then draw_full_page(card) end
  end

  do
    -- Checked first: a bottom-placed favorites block sits past every real
    -- category's own row, so category_at_row would otherwise mistake it for
    -- whichever real category happens to be last.
    local in_favorites = favorites_row_span
      and current_row >= favorites_row_span[1] and current_row <= favorites_row_span[2]
    local in_rejected = rejected_row_span
      and current_row >= rejected_row_span[1] and current_row <= rejected_row_span[2]
    local cat_name = (not in_favorites) and (not in_rejected) and current_row >= full_list_start
      and category_at_row(current_row, category_rows) or nil
    local in_quick_nav = quick_nav_start and current_row >= quick_nav_start and current_row < full_list_start
    if in_favorites or in_rejected or in_quick_nav or cat_name then
      screen.level(0)
      screen.rect(0, 0, 128, 9)
      screen.fill()
      screen.level(15)
      screen.move(1, 7)

      if in_favorites then
        screen.text('Favorites')
      elseif in_rejected then
        screen.text('Rejected')
      elseif cat_name then
        screen.text(titlecase(cat_name))
        local sub_name = subcategory_at_row(current_row, cat_name, subcategory_rows)
        if sub_name then
          screen.move(121, 7)
          screen.text_right(titlecase(sub_name))
        end
      else
        screen.text('Quick Nav')
      end
    end
  end

  do
    local track_top, track_bottom = 0, 63
    screen.level(2)
    screen.move(127, track_top)
    screen.line(127, track_bottom)
    screen.stroke()

    local frac = util.clamp(params:get('pos') / math.max(1, max_pos), 0, 1)
    local thumb_h = 6
    local thumb_y = track_top + frac * (track_bottom - track_top - thumb_h)
    screen.level(15)
    screen.move(127, thumb_y)
    screen.line(127, thumb_y + thumb_h)
    screen.stroke()
  end
end

----------------------------------------------------------------------------
-- Sort Scripts
----------------------------------------------------------------------------

local function sort_card_names()
  local names = {}
  for name, info in pairs(scripts) do
    local fully_sorted = info.category ~= '' and info.subcategory ~= ''
    local skip = (sort_hide_sorted and fully_sorted)
      or (info.rejected and not sort_show_rejected)
    if not skip then
      table.insert(names, name)
    end
  end
  table.sort(names, function(a, b) return display_name(a):lower() < display_name(b):lower() end)
  return names
end

local function build_sort_cards()
  local cards = { { kind = 'legend' } }
  local names = sort_card_names()
  if #names == 0 then
    table.insert(cards, { kind = 'done' })
  else
    for _, name in ipairs(names) do
      table.insert(cards, { kind = 'script', name = name })
    end
  end
  return cards
end

-- The card list is a SNAPSHOT, rebuilt only when entering this screen -- never
-- reactively on every category/subcategory edit. With "only show unsorted" on,
-- sorting the script you're looking at would otherwise yank it (and everything
-- after it) out from under you mid-browse; now it just stays put until you back
-- out to the Sort Scripts menu and come back in.
local sort_cards = build_sort_cards()
-- Set while the "launch this script?" prompt is up; K3 confirms, K2 cancels
-- back to the list instead of all the way out to the menu.
local sort_confirm = false

local function refresh_sort_cards()
  sort_cards = build_sort_cards()
  sort_pos = util.clamp(sort_pos, 1, #sort_cards)
end

local function redraw_sort()
  local cards = sort_cards
  sort_pos = util.clamp(sort_pos, 1, #cards)
  local card = cards[sort_pos]

  if sort_confirm then
    screen.level(15)
    screen.move(64, 20)
    screen.text_center('Do you wish to launch')
    screen.move(64, 30)
    screen.text_center('this script?')
    screen.level(2)
    screen.move(64, 44)
    screen.text_center('to return to freshlook, you')
    screen.move(64, 54)
    screen.text_center('must load the script again')
    screen.level(15)
    screen.move(64, 62)
    screen.text_center('K2 back        K3 launch')
    return
  end

  if card.kind == 'legend' then
    screen.level(2)
    local lines = { 'E1 scroll', 'E2 category   E3 subcategory', 'long K1 reject', 'K2 back', 'K3 launch script' }
    local y = 8
    for _, line in ipairs(lines) do
      screen.move(1, y)
      screen.text(line)
      y = y + line_height
    end
    screen.level(15)
    screen.move(64, 60)
    screen.text_center('vv scroll down vv')
  elseif card.kind == 'done' then
    screen.level(15)
    screen.move(64, 32)
    screen.text_center('everything is sorted. :)')
  elseif card.kind == 'script' then
    local info = scripts[card.name]
    local dim = info.rejected

    screen.level(dim and 4 or 15)
    screen.move(1, 14)
    text_trunc(display_name(card.name), 21)

    screen.level(dim and 2 or 4)
    local y = 14 + line_height
    for _, line in ipairs(wrap_text(info.description or '', full_desc_wrap_chars)) do
      if y > 14 + (line_height * 2) then break end
      screen.move(1, y)
      screen.text(line)
      y = y + line_height
    end

    if info.rejected then
      screen.level(15)
      screen.move(1, 48)
      screen.text('[REJECTED]')
    end

    local cat_label = (info.category ~= '' and info.category) or 'Unsorted'
    local sub_label
    if info.category == '' then
      sub_label = 'Unsorted'
    else
      sub_label = (info.subcategory ~= '' and info.subcategory) or 'Unsorted'
    end

    screen.level(dim and 4 or (cat_label == 'Unsorted' and 4 or 15))
    screen.move(1, 58)
    screen.text(titlecase(cat_label))
    screen.level(dim and 4 or (sub_label == 'Unsorted' and 4 or 15))
    screen.move(121, 58)
    screen.text_right(titlecase(sub_label))
  end

  do
    local track_top, track_bottom = 0, 63
    screen.level(2)
    screen.move(127, track_top)
    screen.line(127, track_bottom)
    screen.stroke()

    local frac = util.clamp((sort_pos - 1) / math.max(1, #cards - 1), 0, 1)
    local thumb_h = 6
    local thumb_y = track_top + frac * (track_bottom - track_top - thumb_h)
    screen.level(15)
    screen.move(127, thumb_y)
    screen.line(127, thumb_y + thumb_h)
    screen.stroke()
  end
end

local function enc_sort(index, delta)
  if sort_confirm then return end
  local cards = sort_cards

  if index == 1 then
    sort_pos = util.clamp(sort_pos + delta, 1, #cards)
    return
  end

  local card = cards[sort_pos]
  if card.kind ~= 'script' then return end
  local info = scripts[card.name]

  if index == 2 then
    local opts = { '' }
    for _, c in ipairs(sorted_category_names()) do table.insert(opts, c) end
    local cur = 1
    for i, c in ipairs(opts) do if c == info.category then cur = i end end
    local new_i = util.clamp(cur + delta, 1, #opts)
    if new_i ~= cur then
      info.category = opts[new_i]
      info.subcategory = ''
      save_fresh_data()
      rebuild_browse_view()
    end
  elseif index == 3 then
    if info.category == '' then return end
    local opts = { '' }
    for _, s in ipairs(sorted_subcategory_names(info.category)) do table.insert(opts, s) end
    local cur = 1
    for i, s in ipairs(opts) do if s == info.subcategory then cur = i end end
    local new_i = util.clamp(cur + delta, 1, #opts)
    if new_i ~= cur then
      info.subcategory = opts[new_i]
      save_fresh_data()
      rebuild_browse_view()
    end
  end
end

--- K1 in Sort Scripts: a plain press toggles whether this script is rejected
--- (excluded from the launcher's own list), no long-press needed.
--- K1 release in Sort Scripts: requires a LONG press, so adjusting category/
--- subcategory with a quick tap can never accidentally also reject a script.
local function sort_key1_release(held)
  if sort_confirm or held < LONG_PRESS_SEC then return end
  local card = sort_cards[sort_pos]
  if not (card and card.kind == 'script') then return end
  local info = scripts[card.name]
  info.rejected = not info.rejected
  save_fresh_data()
  rebuild_browse_view()
end

--- K3 in Sort Scripts: opens the launch-confirm prompt, or (while it's up)
--- confirms and actually loads.
local function sort_key3_press()
  if sort_confirm then
    sort_confirm = false
    local card = sort_cards[sort_pos]
    if card and card.kind == 'script' then
      local file, reason = resolve_script_file(card.name)
      if file then
        norns.script.load(file)
      else
        show_message(reason)
      end
    end
    return
  end

  local card = sort_cards[sort_pos]
  if card and card.kind == 'script' then
    sort_confirm = true
  end
end

----------------------------------------------------------------------------
-- Sort Scripts menu (Auto Sort / Manual Sort / Reset Sorting)
----------------------------------------------------------------------------

local function redraw_sort_menu()
  if sort_menu_state == 'confirm_auto' then
    screen.level(15)
    local lines = {
      'Auto-assigns popular scripts',
      'to a category. Lesser-known',
      'or custom scripts stay',
      'unsorted; already-sorted',
      'scripts stay as they are.',
    }
    local y = 4
    for _, line in ipairs(lines) do
      screen.move(64, y)
      screen.text_center(line)
      y = y + line_height
    end
    screen.level(2)
    screen.move(64, 58)
    screen.text_center('K2 back      K3 auto-sort')
    return
  end

  if sort_menu_state == 'results' and sort_menu_results then
    local r = sort_menu_results
    screen.level(15)
    screen.move(64, 16)
    screen.text_center(r.assigned .. ' scripts auto-assigned')
    screen.move(64, 30)
    screen.text_center(r.already .. ' already sorted by user')
    screen.move(64, 44)
    screen.text_center(r.remain .. ' remain unsorted')
    screen.level(2)
    screen.move(64, 58)
    screen.text_center('K2 / K3 continue')
    return
  end

  if sort_menu_state == 'confirm_reset' then
    screen.level(15)
    local lines = {
      'This will remove all category',
      'and subcategory assignments',
      'from freshlook. Are you sure',
      'you wish to proceed?',
    }
    local y = 10
    for _, line in ipairs(lines) do
      screen.move(64, y)
      screen.text_center(line)
      y = y + line_height
    end
    screen.level(2)
    screen.move(64, 58)
    screen.text_center('K2 back          K3 reset')
    return
  end

  screen.level(4)
  screen.move(64, 10)
  screen.text_center('Sort Scripts')

  local y = 28
  for i, label in ipairs(sort_menu_options) do
    screen.level(sort_menu_pos == i and 15 or 2)
    screen.move(64, y)
    screen.text_center(label)
    y = y + line_height
  end
end

local function enc_sort_menu(index, delta)
  if sort_menu_state then return end
  if index == 3 then
    sort_menu_pos = util.clamp(sort_menu_pos + delta, 1, #sort_menu_options)
  end
end

local function key_sort_menu(index, state)
  if sort_menu_state == 'confirm_auto' then
    if index == 3 then
      sort_menu_results = run_auto_sort()
      sort_menu_state = 'results'
    end
    return
  end

  if sort_menu_state == 'results' then
    if index == 2 or index == 3 then
      sort_menu_state = nil
      sort_menu_results = nil
    end
    return
  end

  if sort_menu_state == 'confirm_reset' then
    if index == 3 then
      reset_sorting()
      sort_menu_state = nil
    end
    return
  end

  if index == 3 then
    if sort_menu_pos == 1 then
      sort_menu_state = 'confirm_auto'
    elseif sort_menu_pos == 2 then
      mode = 'sort_options'
    elseif sort_menu_pos == 3 then
      mode = 'categories'
    else
      sort_menu_state = 'confirm_reset'
    end
  end
end

----------------------------------------------------------------------------
-- Manual Sort options (pre-screen before the actual list)
----------------------------------------------------------------------------

local function redraw_sort_options()
  local rows = {
    { label = 'Show rejected scripts', value = sort_show_rejected },
    { label = 'Only show unsorted', value = sort_hide_sorted },
  }
  local ys = { 10, 20 }
  for i, row in ipairs(rows) do
    screen.level(sort_options_pos == i and 15 or 2)
    screen.move(1, ys[i])
    screen.text(row.label)
    screen.move(121, ys[i])
    screen.text_right(row.value and 'yes' or 'no')
  end

  if sort_hide_sorted then
    screen.level(2)
    screen.move(1, 34)
    screen.text('Note: return to this window')
    screen.move(1, 44)
    screen.text('to refresh hidden list')
  end

  screen.level(2)
  screen.move(64, 61)
  screen.text_center('K2 back          K3 go to list')
end

--- E3 moves between the two rows (clamped -- only two rows, never wraps). E2
--- sets the current row's value by direction rather than flipping it, so
--- spinning the encoder fast in one direction can't flicker yes/no/yes/no
--- from norns sending several enc() ticks per physical detent.
local function enc_sort_options(index, delta)
  if index == 3 then
    sort_options_pos = util.clamp(sort_options_pos + delta, 1, 2)
    return
  end

  if index == 2 then
    local value = delta > 0
    if sort_options_pos == 1 then
      sort_show_rejected = value
    else
      sort_hide_sorted = value
    end
  end
end

local function key_sort_options(index, state)
  if index == 3 then
    mode = 'sort'
    sort_pos = 1
    sort_confirm = false
    refresh_sort_cards()
  end
end

----------------------------------------------------------------------------
-- Define Categories
----------------------------------------------------------------------------

local function build_outline_rows()
  local rows = {}
  table.insert(rows, { kind = 'instructions', text = 'K3: rename / create' })
  table.insert(rows, { kind = 'instructions', text = 'long-press K2: delete' })
  table.insert(rows, { kind = 'blank' })
  table.insert(rows, { kind = 'delete_all' })
  table.insert(rows, { kind = 'restore_all' })
  table.insert(rows, { kind = 'blank' })

  for _, cat in ipairs(sorted_category_names()) do
    table.insert(rows, { kind = 'category', name = cat, count = category_script_count(cat) })
    for _, sub in ipairs(sorted_subcategory_names(cat)) do
      table.insert(rows, { kind = 'subcategory', category = cat, name = sub, count = subcategory_script_count(cat, sub) })
    end
    table.insert(rows, { kind = 'unsorted_sub', category = cat, count = unsorted_subcategory_count(cat) })
    table.insert(rows, { kind = 'add_subcategory', category = cat })
  end

  table.insert(rows, { kind = 'add_category' })
  return rows
end

local function start_text_entry(default, on_done)
  textentry.enter(function(txt)
    if txt and txt ~= '' then on_done(txt) end
    redraw()
  end, default or '')
end

local function categories_key3()
  if cat_message then return end
  if cat_confirm then
    cat_confirm.on_confirm()
    return
  end

  if not cat_selection then return end
  local sel = cat_selection

  if sel.kind == 'category' then
    start_text_entry(sel.name, function(txt)
      if not rename_category(sel.name, txt) then show_message('name taken') end
    end)
  elseif sel.kind == 'subcategory' then
    start_text_entry(sel.name, function(txt)
      if not rename_subcategory(sel.category, sel.name, txt) then show_message('name taken') end
    end)
  elseif sel.kind == 'add_subcategory' then
    start_text_entry('', function(txt)
      if not add_subcategory(sel.category, txt) then show_message('name taken') end
    end)
  elseif sel.kind == 'add_category' then
    start_text_entry('', function(txt)
      if not add_category(txt) then show_message('name taken') end
    end)
  elseif sel.kind == 'delete_all' then
    local cat_count, sub_count = 0, 0
    for _, subs in pairs(categories) do
      cat_count = cat_count + 1
      sub_count = sub_count + #subs
    end

    local function do_delete_all()
      local tags_removed = 0
      for _, info in pairs(scripts) do
        if info.category ~= '' or info.subcategory ~= '' then
          tags_removed = tags_removed + 1
        end
        info.category = ''
        info.subcategory = ''
      end
      deleted_categories_backup = categories
      categories = {}
      save_fresh_data()
      rebuild_browse_view()
      cat_confirm = nil
      cat_message = {
        cat_count .. ' categories deleted',
        sub_count .. ' subcategories deleted',
        tags_removed .. ' scripts had tags removed',
      }
      clock.run(function()
        clock.sleep(3)
        cat_message = nil
        redraw()
      end)
    end

    cat_confirm = {
      message = 'This will delete all the\ncategories, allowing you to\nstart from scratch. It will\nremove all tags.\nAre you sure you wish to\nproceed?',
      on_confirm = function()
        cat_confirm = {
          message = 'Do you wish to make a backup\nof your current JSON file\nbefore proceeding?',
          buttons = 'K2 no        K3 yes',
          on_confirm = function() backup_current_data() do_delete_all() end,
          on_decline = do_delete_all,
        }
      end,
    }
  elseif sel.kind == 'restore_all' then
    cat_confirm = {
      message = 'This will restore default\ncategories. Existing\ncategories will remain.\nScripts must be sorted again.\nContinue?',
      on_confirm = function()
        if deleted_categories_backup then
          for name, subs in pairs(deleted_categories_backup) do
            if not categories[name] then
              categories[name] = subs
            end
          end
          save_fresh_data()
          rebuild_browse_view()
        end
        cat_confirm = nil
      end,
    }
  end
end

local function categories_try_delete()
  if cat_confirm or not cat_selection then return end
  local sel = cat_selection

  if sel.kind == 'category' then
    local count = category_script_count(sel.name)
    local has_subs = #sorted_subcategory_names(sel.name) > 0
    local msg = (count > 0)
      and ('Warning: this category has\nbeen assigned to ' .. count .. ' scripts.\nAre you sure?')
      or ('Delete\ncategory: "' .. sel.name .. '"?')

    cat_confirm = {
      message = msg,
      on_confirm = function()
        if has_subs then
          cat_confirm = {
            message = 'Warning, you are about to\ndelete a category. This will\nremove category and\nsubcategories from ' .. count .. ' scripts.\nAre you really sure?',
            on_confirm = function()
              delete_category(sel.name)
              cat_confirm = nil
            end,
          }
        else
          delete_category(sel.name)
          cat_confirm = nil
        end
      end,
    }
  elseif sel.kind == 'subcategory' then
    local count = subcategory_script_count(sel.category, sel.name)
    local msg = (count > 0)
      and ('Warning: this subcategory\nhas been assigned to ' .. count .. ' scripts.\nAre you sure?')
      or ('Delete\nsubcategory: "' .. sel.name .. '"?')

    cat_confirm = {
      message = msg,
      on_confirm = function()
        delete_subcategory(sel.category, sel.name)
        cat_confirm = nil
      end,
    }
  end
end

local function redraw_categories()
  if cat_message then
    screen.level(15)
    local y = 20
    for _, line in ipairs(cat_message) do
      screen.move(64, y)
      screen.text_center(line)
      y = y + line_height
    end
    return
  end

  if cat_confirm then
    screen.level(15)
    local y = 10
    for line in (cat_confirm.message .. '\n'):gmatch('(.-)\n') do
      screen.move(64, y)
      screen.text_center(line)
      y = y + line_height
    end
    screen.level(2)
    screen.move(64, 58)
    screen.text_center(cat_confirm.buttons or 'K2 cancel        K3 confirm')
    return
  end

  local rows = build_outline_rows()
  local max_pos = math.max(0, #rows - 2)
  cat_pos = util.clamp(cat_pos, 0, max_pos)
  cat_selection = nil

  local index = 2
  local pos = -cat_pos
  local function next_y()
    local y = (pos * line_height) + (line_height * index)
    index = index + 1
    return y
  end

  for _, row in ipairs(rows) do
    local y = next_y()
    local centered = (y == line_height * 3)

    if row.kind == 'instructions' then
      screen.level(2)
      screen.move(1, y)
      screen.text(row.text)
    elseif row.kind == 'category' then
      if centered then cat_selection = row end
      screen.level(centered and 15 or 2)
      screen.move(1, y)
      text_trunc(titlecase(row.name), 20)
      screen.move(121, y)
      screen.text_right('(' .. row.count .. ')')
    elseif row.kind == 'subcategory' then
      if centered then cat_selection = row end
      screen.level(centered and 15 or 2)
      screen.move(8, y)
      text_trunc(titlecase(row.name), 18)
      screen.move(121, y)
      screen.text_right('(' .. row.count .. ')')
    elseif row.kind == 'unsorted_sub' then
      screen.level(1)
      screen.move(8, y)
      screen.text('Unsorted')
      screen.move(121, y)
      screen.text_right('(' .. row.count .. ')')
    elseif row.kind == 'add_subcategory' then
      if centered then cat_selection = row end
      screen.level(centered and 15 or 2)
      screen.move(8, y)
      screen.text('+')
    elseif row.kind == 'add_category' then
      if centered then cat_selection = row end
      screen.level(centered and 15 or 2)
      screen.move(1, y)
      screen.text('+new')
    elseif row.kind == 'delete_all' then
      if centered then cat_selection = row end
      screen.level(centered and 15 or 2)
      screen.move(1, y)
      screen.text('Delete all categories')
    elseif row.kind == 'restore_all' then
      if centered then cat_selection = row end
      screen.level(centered and 15 or 2)
      screen.move(1, y)
      screen.text('Restore all categories')
    end
  end

  do
    local track_top, track_bottom = 0, 63
    screen.level(2)
    screen.move(127, track_top)
    screen.line(127, track_bottom)
    screen.stroke()

    local frac = util.clamp(cat_pos / math.max(1, max_pos), 0, 1)
    local thumb_h = 6
    local thumb_y = track_top + frac * (track_bottom - track_top - thumb_h)
    screen.level(15)
    screen.move(127, thumb_y)
    screen.line(127, thumb_y + thumb_h)
    screen.stroke()
  end
end

----------------------------------------------------------------------------
-- Settings (reachable from the long-press K1 menu) -- everything that used
-- to live in the stock Parameters menu, edited in-app instead.
----------------------------------------------------------------------------

-- `tip` is the lookup key into tooltips_content.txt's "> TOOL TIP: <section>
-- > <tip>" headers -- omitted on rows that don't take part (View Mode has
-- its own NO TOOL TIP entry there, but it's not wired to fire at all since
-- it isn't a plain enable/disable toggle).
local VIEW_ROWS_DEF = {
  { kind = 'option', id = 'opt_view_mode', label = 'View Mode', labels = { 'Compact', 'Expanded', 'Linear' } },
  { kind = 'separator' },
  { kind = 'option', id = 'opt_enable_tooltips', label = 'Enable Tool Tips', labels = { 'yes', 'no' }, tip = 'Enable Tool Tips' },
  { kind = 'option', id = 'opt_show_descriptions', label = 'Show Descriptions', labels = { 'yes', 'no' }, tip = 'Show Descriptions' },
  { kind = 'option', id = 'opt_favorites_before_full', label = 'Favorites Before', labels = { 'yes', 'no' }, tip = 'Favorites Before Full List' },
  { kind = 'note', label = 'Full List' },
  { kind = 'option', id = 'opt_show_instructions', label = 'Show Instructions', labels = { 'yes', 'no' }, tip = 'Show Instructions' },
  { kind = 'option', id = 'opt_show_quick_nav', label = 'Quick Nav', labels = { 'on', 'off' }, tip = 'Quick Nav' },
  -- These two also govern Linear view's category/subcategory rows, so they
  -- stay reachable even with Quick Nav off as long as Linear is selected
  -- (see settings_rows below) -- unlike Full List After Nav and the
  -- favorites-folder option right after it, which are Quick Nav-only.
  { kind = 'option', id = 'opt_hide_empty', label = 'Hide Empty Categories', labels = { 'yes', 'no' }, conditional = 'quick_nav_or_linear', tip = 'Hide Empty Categories' },
  { kind = 'option', id = 'opt_show_quick_nav_count', label = 'Show Quick Nav Count', labels = { 'yes', 'no' }, conditional = 'quick_nav_or_linear', tip = 'Show Quick Nav Count' },
  { kind = 'option', id = 'opt_show_full_after_nav', label = 'Full List After Nav', labels = { 'yes', 'no' }, conditional = true, tip = 'Full List After Nav' },
  { kind = 'option', id = 'opt_favorites_folder_nav', label = 'Favorites Folder', labels = { 'yes', 'no' }, conditional = true, tip = 'Favorites Folder in Quick Nav' },
  { kind = 'note', label = 'in Quick Nav', conditional = true },
}

local FUNCTIONS_ROWS_DEF = {
  { kind = 'option', id = 'opt_show_script_info', label = 'Script Info on Load', labels = { 'yes', 'no' }, tip = 'Script Info on Load' },
  { kind = 'option', id = 'opt_favorites_at_top', label = 'Favorites at Top', labels = { 'yes', 'no' }, tip = 'Favorites at Top (of subcategory)' },
  { kind = 'note', label = 'of subcategory' },
  { kind = 'action', id = 'alphabetize_favorites', label = 'Alphabetize Favorites', tip = 'Alphabetize Favorites' },
  { kind = 'action', id = 'backup_organization', label = 'Backup Organization', tip = 'Backup Organization' },
  { kind = 'action', id = 'replace_home', label = 'Replace Home Screen', tip = 'Replace Home Screen' },
  { kind = 'option', id = 'opt_show_tutorial', label = 'Show Tutorial', labels = { 'yes', 'no' }, tip = 'Show Tutorial' },
}

-- Which of the two row sets above is currently showing -- set when entering
-- from the K1 menu's "View" or "Functions" option.
local settings_kind = 'view'

--- Most Quick Nav sub-options only make sense (and only show) while Quick
--- Nav itself is on; `conditional = 'quick_nav_or_linear'` additionally
--- stays visible whenever Linear view is selected, since those two also
--- apply there.
local function settings_rows()
  local quick_nav_on = params:get('opt_show_quick_nav') == 1
  local linear_on = params:get('opt_view_mode') == 3
  local row_def = (settings_kind == 'view') and VIEW_ROWS_DEF or FUNCTIONS_ROWS_DEF
  local rows = {}
  for _, row in ipairs(row_def) do
    local visible
    if row.conditional == 'quick_nav_or_linear' then
      visible = quick_nav_on or linear_on
    else
      visible = not row.conditional or quick_nav_on
    end
    if visible then
      table.insert(rows, row)
    end
  end
  return rows
end

local function redraw_settings()
  if settings_message then
    screen.level(15)
    screen.move(64, 28)
    screen.text_center(settings_message[1])
    screen.move(64, 38)
    screen.text_center(settings_message[2])
    return
  end

  if settings_confirm then
    screen.level(15)
    local lines = {
      'This will alphabetize your',
      'favorites in the norns main',
      'browser. Do you wish to',
      'proceed?',
    }
    local y = 12
    for _, line in ipairs(lines) do
      screen.move(64, y)
      screen.text_center(line)
      y = y + line_height
    end
    screen.level(2)
    screen.move(64, 58)
    screen.text_center('K2 back      K3 alphabetize')
    return
  end

  local rows = settings_rows()
  -- index starts at 3 (not Categories outline's 2) so that with settings_pos
  -- at its minimum (0), row 1 -- not row 2 -- is the one centered/selected.
  -- Categories' outline gets away with starting at 2 because it has its own
  -- leading instruction rows to absorb that offset; these lists don't.
  local max_pos = math.max(0, #rows - 1)
  settings_pos = util.clamp(settings_pos, 0, max_pos)
  settings_selection = nil

  local index = 3
  local pos = -settings_pos
  local function next_y()
    local y = (pos * line_height) + (line_height * index)
    index = index + 1
    return y
  end

  for _, row in ipairs(rows) do
    local y = next_y()
    local centered = (y == line_height * 3)

    if row.kind == 'separator' then
      screen.level(2)
      screen.move(0, y)
      screen.line(127, y)
      screen.stroke()
    elseif row.kind == 'option' then
      if centered then settings_selection = row end
      screen.level(centered and 15 or 2)
      screen.move(1, y)
      text_trunc(row.label, 20)
      screen.move(121, y)
      screen.text_right(row.labels[params:get(row.id)])
    elseif row.kind == 'action' then
      if centered then settings_selection = row end
      screen.level(centered and 15 or 2)
      screen.move(1, y)
      screen.text(row.label)
    elseif row.kind == 'note' then
      screen.level(2)
      screen.move(1, y)
      screen.text(row.label)
    end
  end

  do
    local track_top, track_bottom = 0, 63
    screen.level(2)
    screen.move(127, track_top)
    screen.line(127, track_bottom)
    screen.stroke()

    local frac = util.clamp(settings_pos / math.max(1, max_pos), 0, 1)
    local thumb_h = 6
    local thumb_y = track_top + frac * (track_bottom - track_top - thumb_h)
    screen.level(15)
    screen.move(127, thumb_y)
    screen.line(127, thumb_y + thumb_h)
    screen.stroke()
  end
end

--- E3 scrolls (clamped, matching Manual Sort's options screen); E2 sets the
--- current option's value by direction rather than flipping it.
local function enc_settings(index, delta)
  if settings_confirm then return end

  if index == 3 then
    local rows = settings_rows()
    local max_pos = math.max(0, #rows - 1)
    settings_pos = util.clamp(settings_pos + delta, 0, max_pos)
  elseif index == 2 then
    if settings_selection and settings_selection.kind == 'option' then
      local labels = settings_selection.labels
      -- A 2-value option is a direction-as-switch (right always lands on
      -- "yes"/label 1, left always on label 2, unchanged from before this
      -- had to support anything else). 3+ values (View Mode's new Linear)
      -- can't map a direction to one absolute value, so those step
      -- relative to wherever they currently are, clamped like E3.
      local new_val
      if #labels <= 2 then
        new_val = delta > 0 and 1 or 2
      else
        new_val = util.clamp(params:get(settings_selection.id) + (delta > 0 and 1 or -1), 1, #labels)
      end
      if tooltip_for(settings_selection) then
        -- Don't flip the param here -- a tool tip takes over instead, and
        -- only its own final slide's enable/disable action (see
        -- tooltip_run_action) actually commits the change. Backing out of
        -- the tool tip must leave the row exactly as it was.
        tooltip_row = settings_selection
        tooltip_index = 1
        tooltip_substate = nil
        mode = 'tooltip'
      else
        params:set(settings_selection.id, new_val)
        if settings_selection.id == 'opt_show_tutorial' then
          -- The real gate lives in data.json (see save_fresh_data), not
          -- the pset -- same reasoning as tutorial_end().
          tutorial_seen = (new_val == 2)
          save_fresh_data()
          if new_val == 1 then
            -- Flipping this to "yes" from Functions is the "watch it
            -- again" entry point -- launch it now rather than just
            -- arming it for next boot.
            mode = 'tutorial'
            tutorial_index = 1
            tutorial_substate = nil
            tutorial_autosort_results = nil
            tutorial_backing = false
          end
        end
      end
    end
  end
end

local function key_settings(index, state)
  if settings_confirm then
    if index == 3 then
      alphabetize_favorites()
      settings_confirm = nil
      settings_message = { 'favorites sorted', 'alphabetically' }
      clock.run(function()
        clock.sleep(2)
        settings_message = nil
        redraw()
      end)
    end
    return
  end

  if index == 3 and settings_selection and settings_selection.kind == 'action' then
    local tip = tooltip_for(settings_selection)
    if tip then
      tooltip_row = settings_selection
      tooltip_index = 1
      tooltip_substate = nil
      mode = 'tooltip'
    elseif settings_selection.id == 'backup_organization' then
      local filename = backup_current_data()
      settings_message = { 'Backup saved as', filename }
      clock.run(function()
        clock.sleep(2)
        settings_message = nil
        redraw()
      end)
    elseif settings_selection.id == 'replace_home' then
      mode = 'replace_home'
      replace_home_index = 1
    else
      settings_confirm = true
    end
  end
end

----------------------------------------------------------------------------
-- Onboarding tutorial (auto-shown on a genuinely fresh install; re-watchable
-- any time via the "Show Tutorial" toggle in Functions).
----------------------------------------------------------------------------

-- Each window's `k2`/`k3` names an action above; nil means the ordinary
-- "back one window" / "proceed one window" default. `no_k2` hides the K2
-- button entirely (a couple of windows are K3-only by design).
--
-- The real content lives in tutorial_content.txt (same folder, plain text,
-- hand-editable -- see the comment header in that file for the format) so
-- it can be rewritten or resliced into new windows without touching this
-- script. This table is only the fallback used if that file is ever
-- missing or fails to parse.
local TUTORIAL_WINDOWS_FALLBACK = {
  {
    paragraphs = { "Welcome to freshlook. Do you want to learn how it works?" },
    k2_label = 'No', k2 = 'end',
    k3_label = "Yes, let's learn",
  },
  {
    paragraphs = { "Long-press K1 any time to end this tutorial." },
  },
}

--- Core of the "## slide" format shared by tutorial_content.txt,
--- replace_home_content.txt, and tooltips_content.txt -- consumes an
--- iterator of lines (a file handle's own :lines(), or a plain array
--- iterator over one section of a bigger file) and returns the parsed
--- windows, or nil if there were none. Slides are numbered purely by the
--- order their "## slide" lines appear -- inserting/deleting/reordering a
--- block is enough, no manual renumbering needed. Within a slide's body,
--- consecutive non-blank lines are word-wrapped together as one
--- paragraph; a blank line forces an actual line break (starts a new
--- paragraph) instead of being discarded.
local function parse_slide_windows(lines_iter)
  local windows = {}
  local current = nil
  local in_meta = true

  -- Appends to the last paragraph while it's still "open" (no blank line
  -- has closed it yet); starts a fresh one otherwise.
  local function current_para()
    local paras = current.paragraphs
    if #paras == 0 or paras[#paras].closed then
      table.insert(paras, { lines = {}, closed = false })
    end
    return paras[#paras]
  end

  for line in lines_iter do
    local inline_text = line:match('^##%s*slide%s+(%S.*)$')
    if inline_text or line:match('^##') then
      current = { paragraphs = {} }
      table.insert(windows, current)
      in_meta = true
      if inline_text then
        -- Text typed on the same line as the delimiter (e.g. "## slide
        -- foo") used to vanish silently -- treat it as the first body line
        -- instead of discarding it.
        in_meta = false
        table.insert(current_para().lines, inline_text)
      end
    elseif current then
      if line:match('^%s*#') then
        -- full-line comment, ignored anywhere
      elseif in_meta then
        -- %w (not just %a) in the key class -- several control keys
        -- (k2_label, k3, no_k2, ...) contain digits.
        local key, val = line:match('^(%a[%w_]*):%s*(.-)%s*$')
        if key == 'k2_label' then current.k2_label = val
        elseif key == 'k3_label' then current.k3_label = val
        elseif key == 'k2' then current.k2 = val ~= '' and val or nil
        elseif key == 'k3' then current.k3 = val ~= '' and val or nil
        elseif key == 'no_k2' then current.no_k2 = (val == 'true')
        elseif key == 'align' then current.align = val
        elseif key == 'outline' then current.outline = (val == 'true')
        elseif line:match('%S') then
          -- first line that isn't a recognized control -- body starts here
          in_meta = false
          table.insert(current_para().lines, line)
        end
      elseif line:match('%S') then
        table.insert(current_para().lines, line)
      elseif #current.paragraphs > 0 then
        -- blank line: close off the paragraph in progress (if any), so the
        -- next non-blank line starts a fresh one -- a forced line break.
        current.paragraphs[#current.paragraphs].closed = true
      end
    end
  end

  if #windows == 0 then return nil end
  for _, w in ipairs(windows) do
    local strings = {}
    for _, para in ipairs(w.paragraphs) do
      if #para.lines > 0 then
        table.insert(strings, table.concat(para.lines, ' '))
      end
    end
    w.paragraphs = strings
  end
  return windows
end

--- Parses a whole file (tutorial_content.txt / replace_home_content.txt)
--- as one slide sequence. Returns nil if the file is missing or empty.
local function load_tutorial_content(filename)
  local path = norns.state.path .. filename
  if not util.file_exists(path) then return nil end
  local file = io.open(path, 'r')
  if not file then return nil end
  local windows = parse_slide_windows(file:lines())
  file:close()
  return windows
end

--- Parses tooltips_content.txt: one slide sequence per
--- "> TOOL TIP: <section> > <label>" header, keyed purely by <label> (the
--- section is only there for the document's own readability). A section
--- whose first non-blank line is "NO TOOL TIP" is recorded with no
--- windows, same effect as the label never appearing in the file at all.
--- Returns nil if the file is missing or defines nothing.
local function load_tooltips_content()
  local path = norns.state.path .. 'tooltips_content.txt'
  if not util.file_exists(path) then return nil end
  local file = io.open(path, 'r')
  if not file then return nil end

  local tooltips = {}
  local label, section_lines, no_tip = nil, nil, false

  local function flush()
    if not label then return end
    if no_tip then
      tooltips[label] = { no_tip = true }
    else
      local i = 0
      local windows = parse_slide_windows(function()
        i = i + 1
        return section_lines[i]
      end)
      if windows then tooltips[label] = { windows = windows } end
    end
  end

  for line in file:lines() do
    local heading = line:match('^>%s*TOOL TIP:%s*(.+)$')
    if heading then
      flush()
      label = heading:match('>%s*(.+)$') or heading
      section_lines = {}
      no_tip = false
    elseif label then
      if line:match('^NO TOOL TIP') then no_tip = true end
      -- The "====...====" lines separating one tool tip from the next in
      -- the document would otherwise get collected as the previous
      -- section's own trailing content and show up inside its last slide.
      if not line:match('^=+%s*$') then
        table.insert(section_lines, line)
      end
    end
  end
  flush()
  file:close()

  if next(tooltips) == nil then return nil end
  return tooltips
end

-- Reassigned in init() once norns.state.path is safe to read (same timing
-- as categories/scripts via load_fresh_data()); the fallback covers every
-- reference to TUTORIAL_WINDOWS that could theoretically run before that.
local TUTORIAL_WINDOWS = TUTORIAL_WINDOWS_FALLBACK

--- Setting this to "no" is what makes the tutorial not auto-show again --
--- finishing window 20 and ending early both go through here.
local function tutorial_end()
  params:set('opt_show_tutorial', 2)
  -- The real gate (see save_fresh_data's comment) -- written immediately,
  -- not deferred to cleanup(), since norns hardware testing often means
  -- power-cycling or restarting mid-session rather than a clean unload.
  tutorial_seen = true
  save_fresh_data()
  mode = 'browse'
  tutorial_substate = nil
  tutorial_autosort_results = nil
  tutorial_backing = false
end

local function tutorial_advance(step)
  step = step or 1
  if tutorial_index + step > #TUTORIAL_WINDOWS then
    tutorial_end()
  else
    tutorial_index = tutorial_index + step
    tutorial_outline_pos = 0
  end
end

--- The one and only way to move backward -- a pure index decrement, no
--- side effects, so a run of these can never re-trigger a script.
local function tutorial_step_back()
  if tutorial_index > 1 then
    tutorial_index = tutorial_index - 1
    tutorial_outline_pos = 0
  end
  tutorial_backing = true
end

local function tutorial_run_action(action)
  if action == 'end' then
    tutorial_end()
  elseif action == 'back' then
    tutorial_step_back()
  elseif action == 'disable_quicknav' then
    params:set('opt_show_quick_nav', 2)
    tutorial_advance()
  elseif action == 'alphabetize' then
    alphabetize_favorites()
    tutorial_advance()
  elseif action == 'replace_home' then
    perform_replace_home()
    tutorial_advance()
  elseif action == 'autosort' then
    tutorial_autosort_results = run_auto_sort()
    tutorial_substate = 'autosort_results'
  elseif action == 'skip_next' then
    -- Declining an action whose very next slide only makes sense once
    -- that action ran (a "Done, ..." follow-up) -- skip past it too.
    tutorial_advance(2)
  else -- 'next' or nil
    tutorial_advance()
  end
end

--- Reads categories straight from the bundled factory_data.json -- never
--- the live (and possibly since-edited, or even cleared via Define
--- Categories) `categories` table -- so the tutorial's outline slide
--- always shows the real shipped defaults no matter what state the
--- user's own install is actually in. Cached after the first read.
local factory_categories_cache = nil
local function load_factory_categories()
  if factory_categories_cache then return factory_categories_cache end
  local path = norns.state.path .. 'factory_data.json'
  if util.file_exists(path) then
    local file = io.open(path, 'rb')
    local content = file:read('*all')
    file:close()
    local ok, decoded = pcall(json.decode, content)
    if ok and decoded and decoded.categories then
      factory_categories_cache = decoded.categories
      return factory_categories_cache
    end
  end
  return {}
end

--- The factory category/subcategory tree, names only -- no counts, no
--- [empty] markers. Used by a tutorial slide with `outline: true` to show
--- what a fresh install actually looks like.
local function build_default_outline_rows()
  local factory_categories = load_factory_categories()
  local names = {}
  for name in pairs(factory_categories) do table.insert(names, name) end
  table.sort(names, function(a, b) return a:lower() < b:lower() end)

  local rows = {}
  for _, name in ipairs(names) do
    table.insert(rows, { text = titlecase(name), indent = 0 })
    for _, sub in ipairs(factory_categories[name]) do
      table.insert(rows, { text = titlecase(sub), indent = 1 })
    end
  end
  return rows
end

local OUTLINE_VISIBLE_ROWS = 5

--- An `outline: true` slide's own body paragraphs (left-aligned, wrapped)
--- followed by a blank row and the live category outline -- all one
--- continuous list, scrolled together with E3.
local function build_outline_slide_rows(win)
  local rows = {}
  for _, para in ipairs(win.paragraphs) do
    for _, line in ipairs(wrap_text(para, 24)) do
      table.insert(rows, { text = line, indent = 0 })
    end
  end
  table.insert(rows, { text = '', indent = 0 })
  for _, row in ipairs(build_default_outline_rows()) do
    table.insert(rows, row)
  end
  return rows
end

local function redraw_tutorial()
  screen.level(2)
  screen.move(2, 7)
  screen.text(tutorial_index .. '/' .. #TUTORIAL_WINDOWS)

  if tutorial_substate == 'autosort_results' and tutorial_autosort_results then
    local r = tutorial_autosort_results
    screen.level(15)
    screen.move(64, 20)
    screen.text_center(r.assigned .. ' scripts auto-assigned')
    screen.move(64, 32)
    screen.text_center(r.already .. ' already sorted by user')
    screen.move(64, 44)
    screen.text_center(r.remain .. ' remain unsorted')
    screen.level(2)
    screen.move(64, 58)
    screen.text_center('K2 / K3 continue')
    return
  end

  local win = TUTORIAL_WINDOWS[tutorial_index]

  if win.outline then
    local rows = build_outline_slide_rows(win)
    local max_offset = math.max(0, #rows - OUTLINE_VISIBLE_ROWS)
    tutorial_outline_pos = util.clamp(tutorial_outline_pos, 0, max_offset)
    local y = 14
    for i = tutorial_outline_pos + 1, math.min(#rows, tutorial_outline_pos + OUTLINE_VISIBLE_ROWS) do
      local row = rows[i]
      screen.level(row.indent > 0 and 4 or 15)
      screen.move(1 + row.indent * 8, y)
      screen.text(row.text)
      y = y + line_height
    end
  else
    -- Same size as the rest of the app -- legible, not shrunk to fit. A
    -- slide with too much text to fit will just run off the bottom edge;
    -- that's a cue to shorten it in tutorial_content.txt, not a bug to
    -- work around by shrinking the font.
    local y = 14
    for _, para in ipairs(win.paragraphs) do
      for _, line in ipairs(wrap_text(para, 24)) do
        draw_line_with_freshlook_highlighted(y, line, win.align)
        y = y + line_height
      end
    end
  end

  screen.level(2)
  screen.move(64, 59)
  local k3_label = win.k3_label or 'proceed'
  if win.no_k2 then
    screen.text_center('K3 ' .. k3_label)
  else
    local k2_label = win.k2_label or 'back'
    screen.text_center('K2 ' .. k2_label .. '      K3 ' .. k3_label)
  end
end

local function key_tutorial(index, state)
  if index == 1 then
    if state == 1 then
      k1_press_time = util.time()
    else
      if k1_press_time and util.time() - k1_press_time >= LONG_PRESS_SEC then
        tutorial_end()
      end
      k1_press_time = nil
    end
    return
  end

  if state ~= 1 then return end

  if tutorial_substate == 'autosort_results' then
    if index == 2 or index == 3 then
      tutorial_substate = nil
      tutorial_autosort_results = nil
      tutorial_advance()
    end
    return
  end

  local win = TUTORIAL_WINDOWS[tutorial_index]
  if index == 2 then
    if tutorial_backing then
      -- Mid backward run -- keep retreating regardless of this slide's own
      -- K2 meaning (a Yes/No prompt, End Tutorial, Disable Now, or even a
      -- hidden K2), so repeated presses reach slide 1 without bouncing off
      -- a prompt or re-triggering its action.
      tutorial_step_back()
    elseif win.no_k2 then
      -- K2 unavailable on this slide when reached moving forward.
    elseif win.k2 then
      tutorial_run_action(win.k2)
    else
      tutorial_step_back()
    end
  elseif index == 3 then
    tutorial_backing = false
    tutorial_run_action(win.k3)
  end
end

----------------------------------------------------------------------------
-- "Replace Home Screen" guide (Functions > Replace Home Screen) -- same
-- slide-engine look as the onboarding tutorial, its own short sequence,
-- ending by running perform_replace_home(). Content lives in
-- replace_home_content.txt (same format/loader as the tutorial's own file);
-- this is only the fallback if that's ever missing.
----------------------------------------------------------------------------

local REPLACE_HOME_WINDOWS_FALLBACK = {
  { paragraphs = { "This will move freshlook to the top of your script list." } },
  {
    k2_label = 'No', k2 = 'end',
    k3_label = 'Yes', k3 = 'replace_home',
    paragraphs = { "Would you like to proceed?" },
  },
  { paragraphs = { "Done." }, k3_label = 'Finish', k3 = 'end' },
}
local REPLACE_HOME_WINDOWS = REPLACE_HOME_WINDOWS_FALLBACK

local function replace_home_end()
  mode = 'settings'
  settings_kind = 'functions'
end

local function replace_home_advance()
  if replace_home_index >= #REPLACE_HOME_WINDOWS then
    replace_home_end()
  else
    replace_home_index = replace_home_index + 1
  end
end

local function redraw_replace_home()
  screen.level(2)
  screen.move(2, 7)
  screen.text(replace_home_index .. '/' .. #REPLACE_HOME_WINDOWS)

  local win = REPLACE_HOME_WINDOWS[replace_home_index]

  local y = 14
  for _, para in ipairs(win.paragraphs) do
    for _, line in ipairs(wrap_text(para, 24)) do
      draw_line_with_freshlook_highlighted(y, line, win.align)
      y = y + line_height
    end
  end

  screen.level(2)
  screen.move(64, 59)
  local k3_label = win.k3_label or 'proceed'
  if win.no_k2 then
    screen.text_center('K3 ' .. k3_label)
  else
    local k2_label = win.k2_label or 'back'
    screen.text_center('K2 ' .. k2_label .. '      K3 ' .. k3_label)
  end
end

local function replace_home_run_action(action)
  if action == 'end' then
    replace_home_end()
  elseif action == 'back' then
    if replace_home_index > 1 then replace_home_index = replace_home_index - 1 end
  elseif action == 'replace_home' then
    perform_replace_home()
    replace_home_advance()
  else -- 'next' or nil
    replace_home_advance()
  end
end

local function key_replace_home(index, state)
  if index == 1 then
    if state == 1 then
      k1_press_time = util.time()
    else
      if k1_press_time and util.time() - k1_press_time >= LONG_PRESS_SEC then
        replace_home_end()
      end
      k1_press_time = nil
    end
    return
  end

  if state ~= 1 then return end

  local win = REPLACE_HOME_WINDOWS[replace_home_index]
  if index == 2 then
    if win.no_k2 then
      -- unavailable on this slide
    else
      replace_home_run_action(win.k2 or 'back')
    end
  elseif index == 3 then
    replace_home_run_action(win.k3)
  end
end

----------------------------------------------------------------------------
-- Tool tips -- fires from Settings right after a toggle flip (E2) or an
-- action select (K3), same slide-engine style as the tutorial. Its final
-- slide's own k2:/k3: control lines are what actually commit the change
-- (enable/disable the row's own param, or run the row's real action);
-- declining just leaves the row as it was. Content lives in
-- tooltips_content.txt; there's no fallback table here -- a row simply
-- gets no tool tip if that file is missing, same as a NO TOOL TIP entry.
----------------------------------------------------------------------------

--- nil if tool tips are off globally, or this row has none defined -- the
--- one check both the toggle (enc_settings) and action (key_settings)
--- trigger points need before entering mode = 'tooltip'.
function tooltip_for(row)
  if not opt_on('opt_enable_tooltips') then return nil end
  local tip = row.tip and TOOLTIPS[row.tip]
  return (tip and tip.windows) and tip or nil
end

local function tooltip_end()
  mode = 'settings'
  tooltip_substate = nil
  tooltip_backup_filename = nil
end

local function tooltip_advance(step)
  step = step or 1
  local windows = TOOLTIPS[tooltip_row.tip].windows
  if tooltip_index + step > #windows then
    tooltip_end()
  else
    tooltip_index = tooltip_index + step
  end
end

local function tooltip_run_action(action)
  if action == 'end' then
    tooltip_end()
  elseif action == 'back' then
    -- Already at the first slide -- nothing further to go back to, so
    -- back out of the tool tip entirely instead of just no-opping.
    if tooltip_index > 1 then
      tooltip_index = tooltip_index - 1
    else
      tooltip_end()
    end
  elseif action == 'enable' then
    params:set(tooltip_row.id, 1)
    if tooltip_row.id == 'opt_show_tutorial' then
      -- The real gate lives in data.json -- see save_fresh_data's comment.
      tutorial_seen = false
      save_fresh_data()
      mode = 'tutorial'
      tutorial_index = 1
      tutorial_substate = nil
      tutorial_autosort_results = nil
      tutorial_backing = false
    else
      tooltip_advance()
    end
  elseif action == 'disable' then
    params:set(tooltip_row.id, 2)
    if tooltip_row.id == 'opt_show_tutorial' then
      tutorial_seen = true
      save_fresh_data()
    end
    tooltip_advance()
  elseif action == 'disable_quicknav' then
    params:set('opt_show_quick_nav', 2)
    tooltip_advance()
  elseif action == 'alphabetize' then
    alphabetize_favorites()
    tooltip_advance()
  elseif action == 'replace_home' then
    perform_replace_home()
    tooltip_advance()
  elseif action == 'backup' then
    tooltip_backup_filename = backup_current_data()
    tooltip_substate = 'backup_result'
  elseif action == 'skip_next' then
    tooltip_advance(2)
  else -- 'next' or nil
    tooltip_advance()
  end
end

local function redraw_tooltip()
  if tooltip_substate == 'backup_result' and tooltip_backup_filename then
    screen.level(15)
    screen.move(64, 24)
    screen.text_center('Backup saved as')
    screen.move(64, 36)
    screen.text_center(tooltip_backup_filename)
    screen.level(2)
    screen.move(64, 58)
    screen.text_center('K2 / K3 continue')
    return
  end

  local windows = TOOLTIPS[tooltip_row.tip].windows
  screen.level(2)
  screen.move(2, 7)
  screen.text(tooltip_index .. '/' .. #windows)

  local win = windows[tooltip_index]

  local y = 14
  for _, para in ipairs(win.paragraphs) do
    for _, line in ipairs(wrap_text(para, 24)) do
      draw_line_with_freshlook_highlighted(y, line, win.align)
      y = y + line_height
    end
  end

  screen.level(2)
  screen.move(64, 59)
  local k3_label = win.k3_label or 'proceed'
  if win.no_k2 then
    screen.text_center('K3 ' .. k3_label)
  else
    local k2_label = win.k2_label or 'back'
    screen.text_center('K2 ' .. k2_label .. '      K3 ' .. k3_label)
  end
end

local function key_tooltip(index, state)
  if index == 1 then
    if state == 1 then
      k1_press_time = util.time()
    else
      if k1_press_time and util.time() - k1_press_time >= LONG_PRESS_SEC then
        tooltip_end()
      end
      k1_press_time = nil
    end
    return
  end

  if state ~= 1 then return end

  if tooltip_substate == 'backup_result' then
    if index == 2 or index == 3 then
      tooltip_substate = nil
      tooltip_backup_filename = nil
      tooltip_advance()
    end
    return
  end

  local windows = TOOLTIPS[tooltip_row.tip].windows
  local win = windows[tooltip_index]
  if index == 2 then
    if win.no_k2 then
      -- unavailable on this slide
    else
      tooltip_run_action(win.k2 or 'back')
    end
  elseif index == 3 then
    tooltip_run_action(win.k3)
  end
end

----------------------------------------------------------------------------
-- Menu (long-press K1)
----------------------------------------------------------------------------

local function redraw_menu()
  screen.level(4)
  screen.move(64, 10)
  screen.text_center('Settings')

  local y = 28
  for i, label in ipairs(menu_options) do
    screen.level(menu_pos == i and 15 or 2)
    screen.move(64, y)
    screen.text_center(label)
    y = y + line_height
  end
end

local function enc_menu(index, delta)
  if index == 3 then
    menu_pos = util.clamp(menu_pos + delta, 1, #menu_options)
  end
end

local function key_menu(index, state)
  if index ~= 3 then return end
  if menu_pos == 1 then
    mode = 'settings'
    settings_kind = 'view'
    settings_pos = 0
    settings_confirm = nil
  elseif menu_pos == 2 then
    mode = 'settings'
    settings_kind = 'functions'
    settings_pos = 0
    settings_confirm = nil
  else
    mode = 'sort_menu'
    sort_menu_pos = 1
    sort_menu_state = nil
    sort_menu_results = nil
  end
end

----------------------------------------------------------------------------
-- Top-level init / enc / key / redraw
----------------------------------------------------------------------------

function init()
  params:add_number('pos', 'Position', 0, 9999, 0)
  params:hide('pos')

  -- All of these now live in the in-app Settings screen (long-press K1) instead
  -- of the stock Parameters menu -- still real params underneath (for pset
  -- persistence), just hidden from Parameters nav.
  params:add_separator()
  params:add_group("Launcher Options", 12)
  params:add_option("opt_view_mode", "View Mode", { "Compact", "Expanded", "Linear" }, 1)
  params:add_separator()
  params:add_option("opt_show_quick_nav", "Quick Nav", { "on", "off" }, 1)
  params:add_option("opt_show_quick_nav_count", "Show Quick Nav Count", { "yes", "no" }, 1)
  params:add_option("opt_show_full_after_nav", "Full List After Nav", { "yes", "no" }, 1)
  params:add_option("opt_favorites_at_top", "Favorites at Top", { "yes", "no" }, 1)
  params:add_option("opt_show_descriptions", "Show Descriptions", { "yes", "no" }, 1)
  params:add_option("opt_hide_empty", "Hide Empty Categories", { "yes", "no" }, 1)
  params:add_option("opt_show_script_info", "Show Script Info on Load", { "yes", "no" }, 2)
  params:add_option("opt_favorites_before_full", "Favorites Before Full List", { "yes", "no" }, 2)
  params:add_option("opt_favorites_folder_nav", "Favorites Folder in Quick Nav", { "yes", "no" }, 2)
  params:add_option("opt_show_instructions", "Show Instructions", { "yes", "no" }, 1)
  -- Default "yes" so a genuinely fresh install (no saved pset yet) auto-opens
  -- the tutorial once; it flips to "no" itself the moment the tutorial ends
  -- (finished or cut short), and the Functions toggle is the only way back in.
  params:add_option("opt_show_tutorial", "Show Tutorial", { "yes", "no" }, 1)
  params:add_option("opt_enable_tooltips", "Enable Tool Tips", { "yes", "no" }, 1)

  params:read()

  for _, id in ipairs({
    "opt_view_mode", "opt_show_quick_nav", "opt_show_quick_nav_count",
    "opt_show_full_after_nav", "opt_show_descriptions", "opt_hide_empty",
    "opt_show_script_info", "opt_favorites_before_full", "opt_favorites_folder_nav",
    "opt_show_instructions", "opt_show_tutorial", "opt_enable_tooltips",
  }) do
    params:hide(id)
    params:set_action(id, function() redraw() end)
  end
  params:hide("Launcher Options")
  params:hide("opt_favorites_at_top")
  params:set_action("opt_favorites_at_top", function()
    rebuild_browse_view()
    redraw()
  end)
  params:set_action("opt_view_mode", function()
    linear_reset()
    redraw()
  end)

  screen.aa(0)
  screen.level(15)
  screen.line_width(1)
  screen.font_size(type_size)
  redraw()
  screen.ping()

  categories, scripts, deleted_categories_backup, tutorial_seen = load_fresh_data()
  merge_discovered_scripts()
  save_fresh_data()
  rebuild_browse_view()

  TUTORIAL_WINDOWS = load_tutorial_content('tutorial_content.txt') or TUTORIAL_WINDOWS_FALLBACK
  REPLACE_HOME_WINDOWS = load_tutorial_content('replace_home_content.txt') or REPLACE_HOME_WINDOWS_FALLBACK
  TOOLTIPS = load_tooltips_content() or {}

  -- Keep the param in sync with the real (data.json-backed) gate, purely
  -- so the Functions screen displays the right yes/no.
  params:set('opt_show_tutorial', tutorial_seen and 2 or 1)

  if not tutorial_seen then
    mode = 'tutorial'
    tutorial_index = 1
    tutorial_substate = nil
    tutorial_autosort_results = nil
    tutorial_backing = false
  end

  redraw()
end

function enc(index, delta)
  if mode == 'browse' then
    enc_browse(index, delta)
  elseif mode == 'menu' then
    enc_menu(index, delta)
  elseif mode == 'sort_menu' then
    enc_sort_menu(index, delta)
  elseif mode == 'sort_options' then
    enc_sort_options(index, delta)
  elseif mode == 'sort' then
    enc_sort(index, delta)
  elseif mode == 'settings' then
    enc_settings(index, delta)
  elseif mode == 'tutorial' then
    -- The only slide kind that uses an encoder at all: E3 scrolls an
    -- `outline: true` slide's category/subcategory list. Clamping happens
    -- in redraw_tutorial itself (it already needs the row count there).
    if index == 3 then
      local win = TUTORIAL_WINDOWS[tutorial_index]
      if win and win.outline then
        tutorial_outline_pos = tutorial_outline_pos + delta
      end
    end
  elseif mode == 'replace_home' then
    -- no encoder actions in this guide either
  elseif mode == 'tooltip' then
    -- no encoder actions in a tool tip either
  elseif mode == 'categories' and not cat_confirm and not cat_message then
    if index == 3 then
      local rows = build_outline_rows()
      local max_pos = math.max(0, #rows - 2)
      cat_pos = util.clamp(cat_pos + delta, 0, max_pos)
    end
  end

  redraw()
end

function key(index, state)
  -- Fully self-contained (including its own K1 press/release tracking for
  -- "long-press to end tutorial") -- short-circuit before the generic
  -- per-button blocks below, which assume 'browse'/'sort'/etc. modes only.
  if mode == 'tutorial' then
    key_tutorial(index, state)
    redraw()
    return
  end

  if mode == 'replace_home' then
    key_replace_home(index, state)
    redraw()
    return
  end

  if mode == 'tooltip' then
    key_tooltip(index, state)
    redraw()
    return
  end

  if index == 1 and mode == 'browse' then
    if state == 1 then
      k1_press_time = util.time()
    else
      if k1_press_time and util.time() - k1_press_time >= LONG_PRESS_SEC then
        mode = 'menu'
        menu_pos = 1
        redraw()
      end
      k1_press_time = nil
    end
    return
  end

  if index == 1 and mode == 'sort' then
    if state == 1 then
      k1_press_time = util.time()
    else
      local held = k1_press_time and (util.time() - k1_press_time) or 0
      k1_press_time = nil
      sort_key1_release(held)
      redraw()
    end
    return
  end

  if index == 2 then
    if mode == 'categories' then
      if state == 1 then
        k2_press_time = util.time()
        return
      end
      local held = k2_press_time and (util.time() - k2_press_time) or 0
      k2_press_time = nil

      if cat_confirm then
        if cat_confirm.on_decline then
          cat_confirm.on_decline()
        else
          cat_confirm = nil
        end
      elseif held >= LONG_PRESS_SEC then
        categories_try_delete()
      else
        mode = 'sort_menu'
      end
      redraw()
      return
    end

    if state ~= 1 then return end
    if mode == 'browse' then
      if browse_confirm then
        browse_confirm = false
      elseif params:get('opt_view_mode') == 3 then
        key_linear(2, state)
      else
        -- Already sitting at the back target (nothing further "back" to go
        -- to, e.g. never jumped into a section) -- a repeat press instead
        -- goes all the way to the absolute top.
        local target = nav_back_pos
        if params:get('pos') == target then target = 0 end
        params:set('pos', target)
      end
    elseif mode == 'menu' then
      mode = 'browse'
    elseif mode == 'sort_menu' then
      if sort_menu_state then
        sort_menu_state = nil
        sort_menu_results = nil
      else
        mode = 'menu'
      end
    elseif mode == 'sort_options' then
      mode = 'sort_menu'
    elseif mode == 'sort' then
      if sort_confirm then
        sort_confirm = false
      else
        mode = 'sort_options'
      end
    elseif mode == 'settings' then
      if settings_confirm then
        settings_confirm = nil
      else
        mode = 'menu'
      end
    end
    redraw()
    return
  end

  if state ~= 1 then return end

  if mode == 'browse' then
    key_browse(index, state)
  elseif mode == 'menu' then
    key_menu(index, state)
  elseif mode == 'sort_menu' then
    key_sort_menu(index, state)
  elseif mode == 'sort_options' then
    key_sort_options(index, state)
  elseif mode == 'sort' then
    if index == 3 then
      sort_key3_press()
    end
  elseif mode == 'settings' then
    key_settings(index, state)
  elseif mode == 'categories' and index == 3 then
    categories_key3()
  end

  redraw()
end

function redraw()
  screen.clear()
  screen.aa(0)
  screen.font_size(type_size)

  if mode == 'browse' then
    redraw_browse()
  elseif mode == 'menu' then
    redraw_menu()
  elseif mode == 'sort_menu' then
    redraw_sort_menu()
  elseif mode == 'sort_options' then
    redraw_sort_options()
  elseif mode == 'sort' then
    redraw_sort()
  elseif mode == 'settings' then
    redraw_settings()
  elseif mode == 'categories' then
    redraw_categories()
  elseif mode == 'tutorial' then
    redraw_tutorial()
  elseif mode == 'replace_home' then
    redraw_replace_home()
  elseif mode == 'tooltip' then
    redraw_tooltip()
  end

  screen.update()
end

function cleanup()
  params:write()
  save_fresh_data()
end
