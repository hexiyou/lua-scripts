--[[
=============================================================================
 luaprobe.lua  —  通用 Lua 运行时探针 v1.0
=============================================================================
 单文件、零依赖。本身只使用 Lua 5.1 语法,因此可被 5.1/5.2/5.3/5.4/5.5、
 LuaJIT、gopher-lua、Luau 等解析;所有"新语法"的探测都通过 load/loadstring
 加载字符串完成,不会因为语法不兼容而整体加载失败。

 探测内容
   1. 实现识别   PUC-Rio / LuaJIT / gopher-lua / Luau / Ravi,宿主环境指纹
   2. 版本推断   不信任 _VERSION,用 API 存在性 + 语法/语义行为 给 5.1~5.5 打分
   3. 数值模型   整数/浮点子类型、位宽、溢出、tostring/tonumber 行为
   4. 字节码头   解析 string.dump 头:版本/字节序/sizeof(int,size_t,Number...)
   5. JIT / FFI  jit.status、编译器标志、热循环是否真的被编译出 trace、ffi 类型大小
   6. 语法/语义  goto、//、位运算、<const>/<close>、__gc、__len、__pairs、
                 协程 yield 边界、xpcall 传参、错误信息风格 ... 共 100+ 项
   7. 标准库     缺失/多余的函数,兼容层残留(LUA_COMPAT_*),宿主扩展函数
   8. 模块       已加载/preload/搜索路径/常见第三方模块是否可被发现(不执行 require)
   9. 沙箱画像   io/os/debug/load/package.loadlib 是否可用,_G 是否可写
  10. 资源上限   局部变量数、upvalue 数、调用深度、C 栈深度、语法嵌套、unpack 上限
  11. 微基准     (可选) 整数/浮点/调用/表/字符串;LuaJIT 额外对比 jit.on / jit.off

 用法
   lua luaprobe.lua                 # 完整文本报告
   lua luaprobe.lua --json          # JSON 输出
   lua luaprobe.lua --brief         # 只输出概览 + 与判定版本不一致的项
   lua luaprobe.lua --no-bench --no-limits --no-modules
   lua luaprobe.lua --out=report.txt
   (Windows 控制台请先 chcp 65001,或使用 --out / --json)

 嵌入用法 (宿主里没有 print / 想拿结构化结果)
   PROBE_OPTS = { quiet = true }                 -- 也可预先设置全局选项表
   local r = dofile("luaprobe.lua")              -- 或 loadfile(...)(...)
   r.text      -- 报告文本        r.data -- 结构化结果 (summary/info/checks/scores)
   r.json()    -- JSON 字符串
=============================================================================
]]

local PROBE_VERSION = "1.0"
local G = _G or _ENV or (getfenv and getfenv(0)) or {}

local type, pcall, tostring, tonumber, select = type, pcall, tostring, tonumber, select
local pairs, ipairs, rawget, getmetatable, setmetatable = pairs, ipairs, rawget, getmetatable, setmetatable
local sfmt, srep = string.format, string.rep
local tconcat, tsort = table.concat, table.sort
local unpack = table.unpack or unpack
local floor = math.floor

-- 在做任何事之前快照 package.loaded(之后的探测可能会 require 内置模块)
local LOADED0 = {}
if type(package) == "table" and type(package.loaded) == "table" then
  for k, v in pairs(package.loaded) do LOADED0[k] = v end
end

-- ---------------------------------------------------------------------------
-- 选项
-- ---------------------------------------------------------------------------
local OPT = { bench = true, limits = true, modules = true, json = false, brief = false, quiet = false }
do
  local args = { ... }
  for i = 1, #args do
    local a = tostring(args[i])
    if a == "--json" then OPT.json = true
    elseif a == "--no-bench" then OPT.bench = false
    elseif a == "--no-limits" then OPT.limits = false
    elseif a == "--no-modules" then OPT.modules = false
    elseif a == "--brief" then OPT.brief = true
    elseif a == "-q" or a == "--quiet" then OPT.quiet = true
    elseif a:sub(1, 6) == "--out=" then OPT.out = a:sub(7) end
  end
  local po = rawget(G, "PROBE_OPTS")
  if type(po) == "table" then for k, v in pairs(po) do OPT[k] = v end end
end

-- ---------------------------------------------------------------------------
-- 工具函数 (集中放在 P 表里,避免主 chunk 的局部变量/upvalue 过多)
-- ---------------------------------------------------------------------------
local P = {}

function P.B(x) return x and true or false end

-- 按路径取值: P.get("string.pack");对严格模式/代理表用 pcall 保护
function P.get(path)
  local v = G
  for name in path:gmatch("[^%.]+") do
    if type(v) ~= "table" then return nil end
    local cur = v
    local ok, nv = pcall(function() return cur[name] end)
    if not ok or nv == nil then return nil end
    v = nv
  end
  return v
end

P.rawload = loadstring or load

function P.compile(src, name)
  if not P.rawload then return nil, "没有 load/loadstring" end
  local ok, f, err = pcall(P.rawload, src, name or "=probe")
  if not ok then return nil, f end
  return f, err
end

function P.syntax_ok(src)
  local f = P.compile(src)
  return f ~= nil and f ~= false
end

-- 编译并执行字符串,返回 ok, v1, v2, v3
function P.eval(src)
  local f, err = P.compile(src)
  if not f then return false, "compile: " .. tostring(err) end
  local r = { pcall(f) }
  if not r[1] then return false, "runtime: " .. tostring(r[2]) end
  return true, r[2], r[3], r[4]
end

function P.strip_pos(msg)
  msg = tostring(msg)
  msg = msg:gsub("^compile: ", ""):gsub("^runtime: ", "")
  msg = msg:gsub("^[^:\n]*:%d+: ", "")
  return msg
end

function P.hexs(s, n)
  local t = {}
  for i = 1, math.min(#s, n) do t[#t + 1] = sfmt("%02x", s:byte(i)) end
  return tconcat(t, " ")
end

function P.bit_set(n, i) return floor(n / 2 ^ i) % 2 == 1 end

function P.bsearch(lo, hi, okfn)
  if not okfn(lo) then return nil end
  while lo < hi do
    local mid = floor((lo + hi + 1) / 2)
    if okfn(mid) then lo = mid else hi = mid - 1 end
  end
  return lo
end

function P.fmtv(v)
  local t = type(v)
  if t == "boolean" then return v and "是" or "否" end
  if t == "table" then
    local parts = {}
    for i = 1, #v do parts[i] = tostring(v[i]) end
    return tconcat(parts, ", ")
  end
  return tostring(v)
end

-- ---------------------------------------------------------------------------
-- 数据存储
-- ---------------------------------------------------------------------------
local D = { info = {}, order = {}, checks = {}, summary = {} }

local function info(section, key, value)
  if value == nil then return end
  local s = D.info[section]
  if not s then s = {}; D.info[section] = s; D.order[#D.order + 1] = section end
  s[#s + 1] = { key, value }
end

-- ---------------------------------------------------------------------------
-- 版本区间 & 检测登记
-- ---------------------------------------------------------------------------
local VERS = { "5.1", "5.2", "5.3", "5.4", "5.5" }
local VIDX = {}
for i, v in ipairs(VERS) do VIDX[v] = i end

local function parse_ranges(s, mark, map)
  if not s then return end
  for tok in s:gmatch("%S+") do
    local lo_i, hi_i
    local a = tok:match("^(%d%.%d)%+$")
    local x, y = tok:match("^(%d%.%d)%-(%d%.%d)$")
    if a then lo_i, hi_i = VIDX[a], #VERS
    elseif x then lo_i, hi_i = VIDX[x], VIDX[y]
    else lo_i = VIDX[tok]; hi_i = lo_i end
    if lo_i and hi_i then
      for i = lo_i, hi_i do if map[i] == nil then map[i] = mark end end
    end
  end
end

-- core: 该特性"应当存在"的版本区间; compat: 可能因 LUA_COMPAT_* 而残留的区间(存在与否都不扣分)
local function check(group, id, desc, core, compat, fn)
  local spec = {}
  parse_ranges(core, "req", spec)
  parse_ranges(compat, "opt", spec)
  local rec = { group = group, id = id, desc = desc, spec = spec,
                expect = (core or "-") .. (compat and (" ~" .. compat) or "") }
  local ok, res, detail = pcall(fn)
  if not ok then rec.result = false; rec.detail = "error: " .. tostring(res)
  elseif res == nil then rec.result = nil
  else rec.result = res and true or false; rec.detail = detail end
  D.checks[#D.checks + 1] = rec
end

-- 非标准扩展(方言)探测:不参与版本打分
local function ext(id, desc, fn)
  local rec = { group = "ext", id = id, desc = desc, spec = {}, expect = "-", ext = true }
  local ok, res = pcall(fn)
  rec.result = ok and (res and true or false) or false
  D.checks[#D.checks + 1] = rec
end

-- ---------------------------------------------------------------------------
-- 实现识别
-- ---------------------------------------------------------------------------
local IMPL = { kind = "puc", label = "PUC-Rio Lua (或未知的兼容实现)" }
do
  local ver = rawget(G, "_VERSION")
  IMPL.claimed = type(ver) == "string" and ver:match("^Lua (%d+%.%d+)") or nil
  local jv = P.get("jit.version")
  if type(jv) == "string" then
    IMPL.kind = "luajit"; IMPL.label = jv; IMPL.base = "5.1"
  elseif rawget(G, "_GOPHER_LUA_VERSION") then
    IMPL.kind = "gopher"
    IMPL.label = tostring(rawget(G, "_GOPHER_LUA_VERSION")) .. " (Go 实现, Lua 5.1 语义)"; IMPL.base = "5.1"
  elseif ver == "Luau" or (P.get("table.freeze") and rawget(G, "typeof")) then
    IMPL.kind = "luau"; IMPL.label = "Luau (Roblox 方言)"
  elseif rawget(G, "ravi") then
    IMPL.kind = "ravi"
    local rv = P.get("ravi.version")
    IMPL.label = "Ravi " .. (type(rv) == "function" and tostring(select(2, pcall(rv)) or "") or tostring(rv or ""))
  elseif IMPL.claimed then
    IMPL.label = "PUC-Rio " .. tostring(ver)
  end
end

local HOSTS = {
  { "OpenResty / ngx_lua", { "ngx" } }, { "Redis 脚本", { "redis", "redis.call" } },
  { "Neovim", { "vim", "vim.api" } }, { "LÖVE", { "love" } },
  { "Roblox", { "game", "workspace", "typeof" } }, { "魔兽世界插件", { "CreateFrame", "GetBuildInfo" } },
  { "Garry's Mod", { "hook", "concommand" } }, { "NodeMCU", { "node", "gpio" } },
  { "Wireshark", { "Proto", "gui_enabled" } }, { "Pandoc", { "PANDOC_VERSION" } },
  { "Hammerspoon", { "hs" } }, { "AwesomeWM", { "awesome", "client" } },
  { "Defold", { "go", "gui", "vmath" } }, { "Unity xLua/toLua", { "CS" } },
  { "Solar2D/Corona", { "display", "system", "timer" } }, { "Tarantool", { "box", "tarantool" } },
  { "mpv", { "mp" } }, { "Apache mod_lua", { "apache2" } }, { "lighttpd", { "lighty" } },
  { "HAProxy", { "core.register_action" } }, { "VLC", { "vlc" } }, { "LuaTeX", { "tex", "texio" } },
  { "Cocos2d-x", { "cc" } }, { "Premake", { "premake" } },
}

-- ---------------------------------------------------------------------------
-- A. API 存在性 (名称, 核心版本区间, 兼容层可能残留的区间)
-- ---------------------------------------------------------------------------
local API = {
  { "setfenv", "5.1" }, { "getfenv", "5.1" }, { "newproxy", "5.1" },
  { "loadstring", "5.1", "5.2" }, { "unpack", "5.1", "5.2" }, { "module", "5.1", "5.2" },
  { "rawlen", "5.2+" }, { "warn", "5.4+" },
  { "math.pow", "5.1-5.2", "5.3+" }, { "math.cosh", "5.1-5.2", "5.3+" }, { "math.sinh", "5.1-5.2", "5.3+" },
  { "math.tanh", "5.1-5.2", "5.3+" }, { "math.frexp", "5.1-5.2", "5.3+" }, { "math.ldexp", "5.1-5.2", "5.3+" },
  { "math.log10", "5.1-5.2", "5.3+" }, { "math.atan2", "5.1-5.2", "5.3+" },
  { "math.type", "5.3+" }, { "math.tointeger", "5.3+" }, { "math.ult", "5.3+" },
  { "math.maxinteger", "5.3+" }, { "math.mininteger", "5.3+" },
  { "string.pack", "5.3+" }, { "string.unpack", "5.3+" }, { "string.packsize", "5.3+" },
  { "table.getn", "5.1" }, { "table.foreach", "5.1" }, { "table.foreachi", "5.1" },
  { "table.maxn", "5.1", "5.2" }, { "table.pack", "5.2+" }, { "table.unpack", "5.2+" },
  { "table.move", "5.3+" }, { "table.create", "5.5+" },
  { "coroutine.isyieldable", "5.3+" }, { "coroutine.close", "5.4+" },
  { "debug.getfenv", "5.1" }, { "debug.setfenv", "5.1" },
  { "debug.setuservalue", "5.2+" }, { "debug.getuservalue", "5.2+" },
  { "debug.upvalueid", "5.2+" }, { "debug.upvaluejoin", "5.2+" },
  { "debug.setcstacklimit", "5.4", "5.5" },
  { "package.loaders", "5.1", "5.2" }, { "package.searchers", "5.2+" },
  { "package.searchpath", "5.2+" }, { "package.seeall", "5.1", "5.2" },
  { "utf8", "5.3+" }, { "bit32", "5.2", "5.3" },
}
for _, a in ipairs(API) do
  local name = a[1]
  check("api", name, "存在 " .. name, a[2], a[3], function() return P.get(name) ~= nil end)
end

-- ---------------------------------------------------------------------------
-- B. 语法
-- ---------------------------------------------------------------------------
check("syntax", "goto", "goto 语句与 ::标签::", "5.2+", nil, function() return P.syntax_ok("goto l1; ::l1::") end)
check("syntax", "empty_stmt", "空语句 ';;'", "5.2+", nil, function() return P.syntax_ok("local x = 1;; return x") end)
check("syntax", "break_mid", "break 可出现在语句块中间", "5.2+", nil,
  function() return P.syntax_ok("while true do break; local x = 1 end") end)
check("syntax", "idiv_op", "整除运算符 //", "5.3+", nil, function() return P.syntax_ok("return 7 // 2") end)
check("syntax", "bit_ops", "位运算符 & | ~ << >> 以及一元 ~", "5.3+", nil,
  function() return P.syntax_ok("return 1 & 3 | 4 ~ 1 << 2 >> 1, ~1") end)
check("syntax", "hex_float", "十六进制浮点字面量 0x1p4 (5.1 依赖 C 库 strtod)", "5.2+", "5.1",
  function() local ok, v = P.eval("return 0x1p4"); return ok and v == 16 end)
check("syntax", "esc_z", "字符串转义 \\z", "5.2+", nil,
  function() local ok, v = P.eval('return "a\\z   b"'); return ok and v == "ab" end)
check("syntax", "esc_x", "字符串转义 \\xXX", "5.2+", nil,
  function() local ok, v = P.eval('return "\\x41"'); return ok and v == "A" end)
check("syntax", "esc_u", "字符串转义 \\u{XXX}", "5.3+", nil,
  function() local ok, v = P.eval('return "\\u{48}"'); return ok and v == "H" end)
check("syntax", "attribs", "局部变量属性 <const> / <close>", "5.4+", nil,
  function() return P.syntax_ok("local x <const> = 1; return x") end)
check("syntax", "global_decl", "global 声明语句", "5.5+", nil,
  function() return P.syntax_ok("global function __probe_g() end") end)
check("syntax", "ro_loopvar", "for 循环控制变量只读", "5.5+", nil,
  function() return not P.syntax_ok("for i = 1, 2 do i = 5 end") end)

-- ---------------------------------------------------------------------------
-- C. 数值语义
-- ---------------------------------------------------------------------------
check("numeric", "int_subtype", "整数/浮点子类型: tostring(1.0) == '1.0'", "5.3+", nil,
  function() return tostring(1.0) == "1.0" end)
check("numeric", "int_wrap", "整数溢出回绕: maxinteger + 1 == mininteger", "5.3+", nil,
  function()
    local mx, mn = P.get("math.maxinteger"), P.get("math.mininteger")
    return mx ~= nil and mn ~= nil and mx + 1 == mn
  end)
check("numeric", "mod_zero_err", "整数 1 % 0 抛出错误 (而非 nan)", "5.3+", nil,
  function() local ok = P.eval("return 1 % 0"); return not ok end)
check("numeric", "fmt_d_float", "string.format('%d', 3.5) 抛出错误", "5.3+", nil,
  function() return not pcall(string.format, "%d", 3.5) end)
check("numeric", "floor_int", "math.floor 返回整数子类型", "5.3+", nil,
  function() local mt = P.get("math.type"); return mt ~= nil and mt(math.floor(3.5)) == "integer" end)
check("numeric", "str_arith_int", "字符串算术保留整数: '10'+1 为 integer", "5.4+", nil,
  function() local mt = P.get("math.type"); return mt ~= nil and mt("10" + 1) == "integer" end)
check("numeric", "random_zero", "math.random(0) 返回随机整数 (xoshiro)", "5.4+", nil,
  function()
    local mt = P.get("math.type")
    local ok, v = pcall(math.random, 0)
    return ok and mt ~= nil and mt(v) == "integer"
  end)

-- ---------------------------------------------------------------------------
-- D. 字符串库
-- ---------------------------------------------------------------------------
check("string", "rep_sep", "string.rep 支持分隔符参数", "5.2+", nil,
  function() return ("a"):rep(3, ",") == "a,a,a" end)
check("string", "fmt_s_nil", "string.format('%s', nil) 不报错", "5.2+", nil,
  function() local ok, v = pcall(string.format, "%s", nil); return ok and v == "nil" end)
check("string", "fmt_a", "string.format 支持 %a", "5.2+", nil,
  function() local ok, v = pcall(string.format, "%a", 1); return ok and type(v) == "string" and v:find("p") ~= nil end)
check("string", "pat_g_class", "模式字符类 %g", "5.2+", nil, function() return ("ab"):find("%g+") ~= nil end)
check("string", "gmatch_init", "string.gmatch 支持 init 参数", "5.4+", nil,
  function() local n = 0; for _ in ("abc"):gmatch("%a", 2) do n = n + 1 end; return n == 2 end)
check("string", "utf8_charpattern54", "utf8.charpattern 为 5.4 版本(含 \\xFD)", "5.4+", nil,
  function() local cp = P.get("utf8.charpattern"); return cp ~= nil and cp:find("\253", 1, true) ~= nil end)

-- ---------------------------------------------------------------------------
-- E. 表 / 迭代
-- ---------------------------------------------------------------------------
check("table", "insert_bounds", "table.insert 对越界位置报错", "5.2+", nil,
  function() return not pcall(table.insert, { 1, 2, 3 }, 10, "x") end)
check("table", "ipairs_index", "ipairs 遵循 __index 元方法", "5.3+", nil,
  function()
    local t = setmetatable({}, { __index = function(_, i) if i <= 3 then return i * 10 end end })
    local n = 0
    for _ in ipairs(t) do n = n + 1 end
    return n == 3
  end)
check("table", "len_meta", "# 运算符遵循 __len", "5.2+", nil,
  function() return #setmetatable({}, { __len = function() return 42 end }) == 42 end)
check("table", "pairs_meta", "pairs 遵循 __pairs", "5.2+", nil,
  function()
    local t = setmetatable({}, { __pairs = function() return function(_, k) if not k then return 1, 1 end end, nil, nil end })
    local n = 0
    for _ in pairs(t) do n = n + 1 end
    return n == 1
  end)
check("table", "ipairs_meta", "ipairs 遵循 __ipairs", "5.2", "5.3", function()
  local t = setmetatable({}, { __ipairs = function() return function(_, i) if i < 2 then return i + 1, true end end, nil, 0 end })
  local n = 0
  for _ in ipairs(t) do n = n + 1 end
  return n == 2
end)

-- ---------------------------------------------------------------------------
-- F. 元表 / GC
-- ---------------------------------------------------------------------------
check("meta", "gc_table", "__gc 对普通 table 生效", "5.2+", nil, function()
  local ran = false
  local mk = function() setmetatable({}, { __gc = function() ran = true end }) end
  mk()
  collectgarbage(); collectgarbage()
  return ran
end)
check("meta", "le_via_lt", "__le 缺失时回退到 not __lt", "5.1-5.3", "5.4+", function()
  local mt = { __lt = function() return true end }
  local a, b = setmetatable({}, mt), setmetatable({}, mt)
  return (pcall(function() return a <= b end))
end)
check("meta", "name_meta", "__name 影响 tostring", "5.3+", nil,
  function() return tostring(setmetatable({}, { __name = "MyType" })):find("^MyType: ") ~= nil end)
check("meta", "close_meta", "__close 元方法 (to-be-closed 变量)", "5.4+", nil, function()
  local ok, v = P.eval("local ran = false; do local x <close> = setmetatable({}, {__close = function() ran = true end}) end; return ran")
  return ok and v == true
end)

-- ---------------------------------------------------------------------------
-- G. 协程
-- ---------------------------------------------------------------------------
check("coro", "running_ismain", "coroutine.running() 返回 (thread, ismain)", "5.2+", nil,
  function() return select("#", coroutine.running()) == 2 end)
check("coro", "yield_pcall", "可以在 pcall 内部 yield", "5.2+", nil, function()
  local co = coroutine.create(function() pcall(function() coroutine.yield(1) end); return 2 end)
  local ok, v = coroutine.resume(co)
  return ok and v == 1
end)
check("coro", "yield_meta", "可以在元方法 (__index) 内部 yield", "5.2+", nil, function()
  local co = coroutine.create(function()
    local t = setmetatable({}, { __index = function(_, k) return coroutine.yield(k) end })
    return t.foo
  end)
  local ok, v = coroutine.resume(co)
  return ok and v == "foo"
end)
check("coro", "yield_iter", "可以在 for-in 迭代器内部 yield", "5.2+", nil, function()
  local co = coroutine.create(function()
    for _ in function() return coroutine.yield("it") end do break end
  end)
  local ok, v = coroutine.resume(co)
  return ok and v == "it"
end)

-- ---------------------------------------------------------------------------
-- H. 错误处理 / 函数 / 加载 / 调试
-- ---------------------------------------------------------------------------
check("error", "xpcall_args", "xpcall 可向被调函数传参", "5.2+", nil, function()
  local ok, ok2, v = pcall(xpcall, function(a) return a end, function() end, 42)
  return ok and ok2 and v == 42
end)
check("error", "errmsg_new", "错误信息风格: 'attempt to call a nil value (local ...)'", "5.3+", nil, function()
  local ok, e = pcall(function() local x; x() end)
  return type(e) == "string" and e:find("a nil value %(") ~= nil
end)
check("func", "getinfo_nparams", "debug.getinfo(f,'u').nparams", "5.2+", nil, function()
  local i = debug.getinfo(function(a, b) end, "u")
  return i ~= nil and i.nparams == 2
end)
check("func", "getinfo_tail", "debug.getinfo(level,'t').istailcall", "5.2+", nil, function()
  local i = debug.getinfo(1, "t")
  return i ~= nil and i.istailcall ~= nil
end)
check("func", "getinfo_ftransfer", "debug.getinfo(level,'r').ftransfer", "5.4+", nil, function()
  local i = debug.getinfo(1, "r")
  return i ~= nil and i.ftransfer ~= nil
end)
check("func", "load_env", "load(chunk, name, mode, env) 的 env 参数", "5.2+", nil, function()
  local f = P.rawload and P.rawload("return x", "=c", "t", { x = 5 })
  return f ~= nil and f ~= false and f() == 5
end)
check("func", "env_var", "_ENV 词法环境变量", "5.2+", nil, function()
  local ok, v = P.eval("local _ENV = {y = 7}; return y")
  return ok and v == 7
end)
check("func", "load_mode", "load 的 mode 参数 (文本块被 'b' 拒绝)", "5.2+", nil, function()
  local f = P.rawload("return 1", "=c", "b")
  return f == nil
end)

-- ---------------------------------------------------------------------------
-- I. 模块系统 / GC / OS
-- ---------------------------------------------------------------------------
check("pkg", "require_2nd", "require 返回第二个结果 (loader data)", "5.4+", nil, function()
  if type(package) ~= "table" or type(package.preload) ~= "table" or type(require) ~= "function" then return nil end
  package.preload["__probe_mod"] = function() return {} end
  local ok, n = pcall(function() return select("#", require("__probe_mod")) end)
  package.preload["__probe_mod"] = nil
  package.loaded["__probe_mod"] = nil
  return ok and n == 2
end)
check("gc", "gc_isrunning", "collectgarbage('isrunning')", "5.2+", nil,
  function() local ok, v = pcall(collectgarbage, "isrunning"); return ok and type(v) == "boolean" end)
check("gc", "gc_inc_mode", "collectgarbage('incremental') 模式切换选项", "5.2 5.4+", nil,
  function() return (pcall(collectgarbage, "incremental")) end)
check("gc", "gc_param", "collectgarbage('param', ...) 参数接口", "5.5+", nil,
  function() return (pcall(collectgarbage, "param", "pause")) end)
check("os", "execute_bool", "os.execute() 返回 boolean (而非数字)", "5.2+", nil, function()
  if type(os) ~= "table" or type(os.execute) ~= "function" then return nil end
  local ok, v = pcall(os.execute)
  if not ok then return nil end
  return type(v) == "boolean"
end)

-- ---------------------------------------------------------------------------
-- J. 非标准扩展 / 方言 (不参与版本打分)
-- ---------------------------------------------------------------------------
ext("lj_ll_literal", "LuaJIT 64 位整数字面量 1LL / 1ULL", function() return P.syntax_ok("return 1LL, 1ULL") end)
ext("lj_complex_literal", "LuaJIT 复数字面量 1i", function() return P.syntax_ok("return 1i") end)
ext("bin_literal", "二进制字面量 0b101 (Luau 等)", function() return P.syntax_ok("return 0b101") end)
ext("underscore_num", "数字下划线分隔 1_000 (Luau 等)", function() return P.syntax_ok("return 1_000") end)
ext("compound_assign", "复合赋值 x += 1 (Luau / 方言)", function() return P.syntax_ok("local x = 1; x += 1") end)
ext("continue_kw", "continue 关键字 (Luau / GLua)", function() return P.syntax_ok("for i = 1, 2 do continue end") end)
ext("c_not_equal", "C 风格 != / && / || (GLua)", function() return P.syntax_ok("return 1 != 2") end)
ext("c_comment", "C 风格注释 /* */ 或 // (GLua)", function() return P.syntax_ok("/* c */ return 1") end)
ext("type_annotation", "类型标注 local x: number (Luau)", function() return P.syntax_ok("local x: number = 1") end)
ext("if_expression", "if-then-else 表达式 (Luau)", function() return P.syntax_ok("local x = if true then 1 else 2") end)
ext("proper_tailcall", "尾调用不增长栈 (深度 3e5)", function()
  local function f(n) if n == 0 then return true end return f(n - 1) end
  return f(300000) == true
end)
ext("weak_values", "弱引用表 (__mode='v') 在 GC 后被清理", function()
  local t = setmetatable({}, { __mode = "v" })
  t[1] = {}
  collectgarbage(); collectgarbage()
  return t[1] == nil
end)

-- ---------------------------------------------------------------------------
-- 版本打分
-- ---------------------------------------------------------------------------
local function compute_scores()
  local sc = {}
  for i = 1, #VERS do sc[i] = { n = 0, bad = {} } end
  for _, c in ipairs(D.checks) do
    if c.result ~= nil and not c.ext then
      for i = 1, #VERS do
        local e = c.spec[i]
        local pen
        if e == "req" then pen = c.result and 0 or 1
        elseif e == "opt" then pen = 0
        else pen = c.result and 1 or 0 end
        if e ~= "opt" then sc[i].n = sc[i].n + 1 end
        if pen > 0 then sc[i].bad[#sc[i].bad + 1] = c end
      end
    end
  end
  for i = 1, #VERS do
    local s = sc[i]
    s.pct = s.n > 0 and (s.n - #s.bad) / s.n * 100 or 0
  end
  return sc
end

local SC = compute_scores()
local BEST = 1
do
  local top = -1
  for i = 1, #VERS do
    if SC[i].pct > top + 1e-9 then top = SC[i].pct; BEST = i end
  end
  local ci = VIDX[IMPL.claimed or ""]
  if ci and SC[ci].pct >= top - 1e-9 then BEST = ci end
  if IMPL.base then BEST = VIDX[IMPL.base] end       -- LuaJIT / gopher-lua: 以 5.1 为语义基线
end

-- ---------------------------------------------------------------------------
-- 数值模型
-- ---------------------------------------------------------------------------
local function num_type(v)
  local mt = P.get("math.type")
  if type(v) == "number" and mt then return mt(v) or "number" end
  return type(v)
end

local EXPRS = {
  "1/2", "3//2", "-3//2", "3.0//2", "3%-2", "-3%2", "5.5%2", "7//0.0", "1//0", "1%0",
  "2^53", "2^53+1 == 2^53", "2^24+1 == 2^24", "0.1+0.2 == 0.3", "math.maxinteger+1", "math.mininteger",
  "0x7fffffff+1", "0xffffffff", "0x7fffffffffffffff", "0xffffffffffffffff",
  "9223372036854775807", "9223372036854775808", "1e2", "2^63", "1e15", "1e100",
  "math.tointeger(3.0)", "3|0", "'10'+1", "'0x10'+0", "'1e1'+0", "10=='10'", "1<2.5",
  "math.pi", "-0.0", "0/0", "1/0", "-1/0", "#'\\0ab'", "math.abs(-0.0)",
  "tonumber('0x10')", "tonumber(' 10 ')", "tonumber('10',2)", "tonumber('1e2')", "tonumber('0b11')",
  "tonumber('1_0')", "tonumber('inf')", "tonumber('nan')", "tonumber('0x')", "tonumber('')",
  "string.format('%.17g', 0.1)", "string.format('%x', -1)", "string.format('%d', 2^31)",
  "string.format('%5.1f|%-6d|%+d', 3.14159, 42, 7)",
}
do
  local sect = "数值模型"
  local float_bits = (2 ^ 53 + 1 == 2 ^ 53) and "64 位 (double)" or "更宽"
  if 2 ^ 24 + 1 == 2 ^ 24 then float_bits = "32 位 (float)" end
  info(sect, "lua_Number 精度", float_bits)
  local mx = P.get("math.maxinteger")
  if mx then
    info(sect, "lua_Integer 位宽", #sfmt("%x", mx) * 4)
  else
    info(sect, "整数子类型", "无 (所有数字均为 lua_Number)")
  end
  info(sect, "tostring(1) / tostring(1.0)", tostring(1) .. " / " .. tostring(1.0))
  local nan = 0 / 0
  info(sect, "NaN 打印为", tostring(nan))
  for _, e in ipairs(EXPRS) do
    local ok, v = P.eval("return " .. e)
    local out
    if ok then
      out = tostring(v) .. "  [" .. num_type(v) .. "]"
    elseif tostring(v):find("^compile:") then
      out = "(语法不支持)"
    else
      out = "错误: " .. P.strip_pos(v)
    end
    info(sect, e, out)
  end
end

-- ---------------------------------------------------------------------------
-- 字节码头解析
-- ---------------------------------------------------------------------------
function P.dump_header()
  local f = function() return 1 end
  local ok, s = pcall(string.dump, f)
  if not ok or type(s) ~= "string" then return nil, tostring(s) end
  local r = { hex = P.hexs(s, 32), size = #s }
  local b = { s:byte(1, 40) }
  if s:sub(1, 4) == "\27Lua" then
    local v = b[5]
    r.kind = "PUC-Rio"
    r.version = sfmt("%d.%d", floor(v / 16), v % 16)
    r.format = b[6]
    if v == 0x51 or v == 0x52 then
      r.little_endian = (b[7] == 1)
      r.sizeof_int, r.sizeof_size_t, r.sizeof_instruction, r.sizeof_number = b[8], b[9], b[10], b[11]
      r.integral_number = (b[12] == 1)
    elseif v == 0x53 then
      r.sizeof_int, r.sizeof_size_t, r.sizeof_instruction = b[13], b[14], b[15]
      r.sizeof_integer, r.sizeof_number = b[16], b[17]
      r.little_endian = (b[18] == 0x78)
    elseif v == 0x54 then
      r.sizeof_instruction, r.sizeof_integer, r.sizeof_number = b[13], b[14], b[15]
      r.little_endian = (b[16] == 0x78)
    else
      r.note = "该字节码版本的头部布局未解析,请参考 hex"
    end
  elseif s:sub(1, 3) == "\27LJ" then
    local fl = b[5] or 0
    r.kind = "LuaJIT"
    r.version = "BCDUMP v" .. tostring(b[4])
    r.big_endian, r.stripped = P.bit_set(fl, 0), P.bit_set(fl, 1)
    r.has_ffi, r.fr2_gc64 = P.bit_set(fl, 2), P.bit_set(fl, 3)
  else
    r.kind = "未知/非标准字节码"
  end
  local g = P.rawload(s, "=dump")
  r.roundtrip = (g ~= nil and g ~= false and pcall(g))
  local ok2, s2 = pcall(string.dump, f, true)
  r.strip_arg = ok2 and type(s2) == "string" and #s2 < #s
  return r
end

do
  local sect = "字节码"
  local h, err = P.dump_header()
  if not h then
    info(sect, "string.dump", "不可用: " .. tostring(err))
  else
    info(sect, "类型", h.kind)
    info(sect, "字节码版本", h.version)
    info(sect, "format", h.format)
    if h.little_endian ~= nil then info(sect, "字节序", h.little_endian and "小端" or "大端") end
    if h.big_endian ~= nil then info(sect, "字节序", h.big_endian and "大端" or "小端") end
    info(sect, "sizeof(int)", h.sizeof_int)
    info(sect, "sizeof(size_t)", h.sizeof_size_t)
    info(sect, "sizeof(Instruction)", h.sizeof_instruction)
    info(sect, "sizeof(lua_Integer)", h.sizeof_integer)
    info(sect, "sizeof(lua_Number)", h.sizeof_number)
    info(sect, "lua_Number 为整数型", h.integral_number)
    info(sect, "含 FFI 标志", h.has_ffi)
    info(sect, "FR2/GC64 帧布局", h.fr2_gc64)
    info(sect, "示例函数 dump 大小(字节)", h.size)
    info(sect, "dump 后可 load 回并运行", h.roundtrip)
    info(sect, "string.dump 支持 strip 参数", h.strip_arg)
    info(sect, "头部 hex(前32字节)", h.note and (h.hex .. "  (" .. h.note .. ")") or h.hex)
    D.dump = h
  end
end

-- ---------------------------------------------------------------------------
-- 运行时概览 / 宿主 / 平台
-- ---------------------------------------------------------------------------
do
  local sect = "运行时概览"
  info(sect, "_VERSION", rawget(G, "_VERSION"))
  info(sect, "实现", IMPL.label)
  local argt = rawget(G, "arg")
  if type(argt) == "table" then
    info(sect, "解释器 arg[-1]", argt[-1])
    info(sect, "脚本 arg[0]", argt[0])
  end
  if type(collectgarbage) == "function" then
    local ok, kb = pcall(collectgarbage, "count")
    if ok and type(kb) == "number" then info(sect, "启动后 Lua 堆内存", sfmt("%.1f KB", kb)) end
  end
  if type(os) == "table" and type(os.clock) == "function" then
    local t0 = os.clock(); local t1 = t0; local n = 0
    while t1 == t0 and n < 5000000 do t1 = os.clock(); n = n + 1 end
    if t1 ~= t0 then info(sect, "os.clock 最小步长", sfmt("%.3f ms", (t1 - t0) * 1000)) end
  end
  if type(os) == "table" and type(os.setlocale) == "function" then
    local ok, l = pcall(os.setlocale)
    if ok then info(sect, "当前 locale", l) end
  end
  info(sect, "tostring({})", tostring({}))
  info(sect, "tostring(print)", tostring(print))

  local sect2 = "宿主/平台"
  local hosts = {}
  for _, h in ipairs(HOSTS) do
    local all = true
    for _, n in ipairs(h[2]) do if P.get(n) == nil then all = false; break end end
    if all then hosts[#hosts + 1] = h[1] end
  end
  if rawget(G, "channel") and IMPL.kind == "gopher" then hosts[#hosts + 1] = "gopher-lua channel 库" end
  info(sect2, "识别到的宿主环境", #hosts > 0 and hosts or "未发现已知宿主指纹 (可能是独立解释器)")
  local cfg = type(package) == "table" and package.config
  local dirsep = type(cfg) == "string" and cfg:sub(1, 1) or nil
  info(sect2, "目录分隔符", dirsep)
  local cp = type(package) == "table" and package.cpath
  if type(cp) == "string" then info(sect2, "C 模块后缀(cpath)", cp:match("%?%.(%w+)") or cp:match("%.(%w+)") ) end
  local jitos, jitarch = P.get("jit.os"), P.get("jit.arch")
  info(sect2, "jit.os / jit.arch", jitos and (tostring(jitos) .. " / " .. tostring(jitarch)) or nil)
  local guess
  if jitos then guess = tostring(jitos)
  elseif dirsep == "\\" then guess = "Windows"
  elseif type(cp) == "string" and cp:find("%.dll") then guess = "Windows 类 (Cygwin/MSYS 等,目录分隔符为 /)"
  elseif type(cp) == "string" and cp:find("%.dylib") then guess = "macOS"
  elseif dirsep == "/" then guess = "类 Unix" end
  info(sect2, "操作系统推测", guess)
  if type(os) == "table" and type(os.getenv) == "function" then
    local env = {}
    for _, k in ipairs { "OS", "OSTYPE", "MSYSTEM", "CYGWIN", "WSL_DISTRO_NAME", "PROCESSOR_ARCHITECTURE",
                         "LUA_PATH", "LUA_CPATH", "LUA_INIT", "LUA_PATH_5_1", "LUA_PATH_5_2", "LUA_PATH_5_3",
                         "LUA_PATH_5_4", "LUA_CPATH_5_1", "LUA_CPATH_5_3", "LUA_CPATH_5_4", "LUAJIT_ENABLE_LUA52COMPAT" } do
      local ok, v = pcall(os.getenv, k)
      if ok and v and v ~= "" then env[#env + 1] = k .. "=" .. v end
    end
    info(sect2, "相关环境变量", #env > 0 and env or nil)
  end
  local ptr
  if D.dump and D.dump.sizeof_size_t then ptr = D.dump.sizeof_size_t * 8 end
  if not ptr then
    local addr = tostring({}):match("0x(%x+)") or tostring({}):match(": (%x+)")
    if addr then ptr = (#addr > 8) and 64 or 32 end
  end
  info(sect2, "指针宽度(位)", ptr)
end

-- ---------------------------------------------------------------------------
-- JIT / FFI
-- ---------------------------------------------------------------------------
do
  local sect = "JIT"
  local jit = rawget(G, "jit")
  if type(jit) == "table" then
    info(sect, "jit.version", jit.version)
    info(sect, "jit.version_num", jit.version_num)
    info(sect, "jit.os / jit.arch", tostring(jit.os) .. " / " .. tostring(jit.arch))
    if type(jit.status) == "function" then
      local r = { pcall(jit.status) }
      if r[1] then
        info(sect, "JIT 当前启用", r[2] and true or false)
        local flags = {}
        for i = 3, #r do flags[#flags + 1] = tostring(r[i]) end
        info(sect, "CPU 特性 / 优化 flags", flags)
      end
    end
    local members = {}
    for k in pairs(jit) do members[#members + 1] = tostring(k) end
    tsort(members)
    info(sect, "jit.* 成员", members)
    local mods = {}
    for _, name in ipairs { "jit.util", "jit.opt", "jit.profile", "jit.bc", "jit.vmdef",
                            "string.buffer", "table.new", "table.clear", "table.clone", "table.nkeys", "table.isarray" } do
      if (pcall(require, name)) then mods[#mods + 1] = name end
    end
    info(sect, "可 require 的 LuaJIT 扩展模块", mods)
    -- 热循环是否真的被编译出 trace
    local ju = P.get("package.loaded.jit.util") or (pcall(require, "jit.util") and require("jit.util"))
    if type(ju) == "table" and type(ju.traceinfo) == "function" and type(jit.flush) == "function" then
      pcall(jit.flush)
      local function hot() local x = 0; for i = 1, 200000 do x = x + i end; return x end
      hot(); hot()
      local n = 0
      for i = 1, 100 do
        local ok, ti = pcall(ju.traceinfo, i)
        if ok and ti then n = n + 1 else break end
      end
      info(sect, "热循环后已编译 trace 数", n)
      info(sect, "JIT 编译器实际生效", n > 0)
    end
  else
    info(sect, "jit 全局", "不存在 (非 LuaJIT)")
  end
  local rv = rawget(G, "ravi")
  if type(rv) == "table" then
    info(sect, "Ravi: ravi.jit()", (type(rv.jit) == "function") and select(2, pcall(rv.jit)) or nil)
    info(sect, "Ravi: ravi.compile", type(rv.compile) == "function")
  end

  local sect2 = "FFI"
  local okf, ffi = pcall(require, "ffi")
  if okf and type(ffi) == "table" then
    info(sect2, "ffi.os / ffi.arch", tostring(ffi.os) .. " / " .. tostring(ffi.arch))
    local abis = {}
    for _, a in ipairs { "32bit", "64bit", "le", "be", "fpu", "softfp", "hardfp", "eabi", "win", "uwp", "gc64" } do
      local ok, v = pcall(ffi.abi, a)
      if ok and v then abis[#abis + 1] = a end
    end
    info(sect2, "ffi.abi 为真的项", abis)
    local sizes = {}
    for _, t in ipairs { "char", "short", "int", "long", "long long", "float", "double", "long double",
                         "void *", "size_t", "intptr_t", "wchar_t" } do
      local ok, v = pcall(ffi.sizeof, t)
      if ok and v then sizes[#sizes + 1] = t .. "=" .. v end
    end
    info(sect2, "sizeof", sizes)
  else
    info(sect2, "ffi", "不可用")
  end
end

-- ---------------------------------------------------------------------------
-- 标准库完整性 / 宿主扩展
-- ---------------------------------------------------------------------------
local STD = {
  _G = { "_G", "_VERSION", "assert", "collectgarbage", "dofile", "error", "getfenv", "getmetatable", "ipairs", "load",
         "loadfile", "loadstring", "module", "newproxy", "next", "pairs", "pcall", "print", "rawequal", "rawget", "rawlen",
         "rawset", "require", "select", "setfenv", "setmetatable", "tonumber", "tostring", "type", "unpack", "warn",
         "xpcall", "gcinfo", "arg",
         "coroutine", "debug", "io", "math", "os", "package", "string", "table", "utf8", "bit32",
         "jit", "bit", "ffi" },
  string = { "byte", "char", "dump", "find", "format", "gfind", "gmatch", "gsub", "len", "lower", "match", "pack",
             "packsize", "rep", "reverse", "sub", "unpack", "upper" },
  table = { "clear", "clone", "concat", "create", "foreach", "foreachi", "getn", "insert", "maxn", "move", "new", "nkeys",
            "pack", "remove", "setn", "sort", "unpack" },
  math = { "abs", "acos", "asin", "atan", "atan2", "ceil", "cos", "cosh", "deg", "exp", "floor", "fmod", "frexp", "huge",
           "ldexp", "log", "log10", "max", "maxinteger", "min", "mininteger", "mod", "modf", "pi", "pow", "rad", "random",
           "randomseed", "sin", "sinh", "sqrt", "tan", "tanh", "tointeger", "type", "ult" },
  io = { "close", "flush", "input", "lines", "open", "output", "popen", "read", "stderr", "stdin", "stdout", "tmpfile",
         "type", "write" },
  os = { "clock", "date", "difftime", "execute", "exit", "getenv", "remove", "rename", "setlocale", "time", "tmpname" },
  coroutine = { "close", "create", "isyieldable", "resume", "running", "status", "wrap", "yield" },
  debug = { "debug", "getfenv", "gethook", "getinfo", "getlocal", "getmetatable", "getregistry", "getupvalue",
            "getuservalue", "sethook", "setcstacklimit", "setfenv", "setlocal", "setmetatable", "setupvalue",
            "setuservalue", "traceback", "upvalueid", "upvaluejoin" },
  package = { "config", "cpath", "loaded", "loaders", "loadlib", "path", "preload", "searchers", "searchpath", "seeall" },
  utf8 = { "char", "charpattern", "codepoint", "codes", "len", "offset" },
  bit32 = { "arshift", "band", "bnot", "bor", "btest", "bxor", "extract", "lrotate", "lshift", "replace", "rrotate",
            "rshift" },
}
do
  local sect = "标准库"
  local present = {}
  local libs = { "string", "table", "math", "io", "os", "coroutine", "debug", "package", "utf8", "bit32", "bit", "jit", "ffi" }
  for _, name in ipairs(libs) do
    local t = P.get(name)
    if type(t) == "table" then
      local n = 0
      for _ in pairs(t) do n = n + 1 end
      present[#present + 1] = name .. "(" .. n .. ")"
    end
  end
  info(sect, "已存在的库及成员数", present)
  local missing = {}
  for _, name in ipairs { "string", "table", "math", "io", "os", "coroutine", "debug", "package" } do
    if type(P.get(name)) ~= "table" then missing[#missing + 1] = name end
  end
  info(sect, "缺失的基础库 (沙箱裁剪)", #missing > 0 and missing or "无")
  local std_g = {}
  for _, n in ipairs(STD._G) do std_g[n] = true end
  local extra_g = {}
  for k, v in pairs(G) do
    if type(k) == "string" and not std_g[k] then extra_g[#extra_g + 1] = k .. ":" .. type(v) end
  end
  tsort(extra_g)
  info(sect, "宿主/用户添加的全局 (非标准)", #extra_g > 0 and extra_g or "无")
  for _, lib in ipairs { "string", "table", "math", "io", "os", "coroutine", "debug", "package", "utf8" } do
    local t = P.get(lib)
    if type(t) == "table" then
      local known = {}
      for _, n in ipairs(STD[lib]) do known[n] = true end
      local ex = {}
      for k, v in pairs(t) do
        if type(k) == "string" and not known[k] then ex[#ex + 1] = k .. ":" .. type(v) end
      end
      tsort(ex)
      if #ex > 0 then info(sect, lib .. " 库的非标准成员", ex) end
    end
  end
  local mt = getmetatable("")
  info(sect, "字符串元表 __index == string", type(mt) == "table" and mt.__index == string)
end

-- ---------------------------------------------------------------------------
-- 模块
-- ---------------------------------------------------------------------------
local KNOWN_MODULES = {
  "lfs", "socket", "socket.core", "socket.http", "socket.url", "ltn12", "mime", "mime.core", "ssl", "ssl.https",
  "cjson", "cjson.safe", "dkjson", "json", "rapidjson", "lunajson", "cmsgpack", "msgpack", "lpeg", "re", "lpeglabel",
  "lsqlite3", "luasql.sqlite3", "luasql.mysql", "luasql.postgres", "sqlite3", "zlib", "lz4", "lzlib", "md5", "sha1",
  "sha2", "openssl", "lcurl", "curl", "luv", "uv", "posix", "posix.unistd", "posix.sys.stat", "bit", "bit32", "ffi",
  "jit", "jit.util", "string.buffer", "table.new", "table.clear", "table.clone", "lanes", "copas", "coxpcall", "pl",
  "pl.pretty", "pl.utils", "pl.path", "pl.stringx", "ansicolors", "luaunit", "busted", "luassert", "inspect", "serpent",
  "middleclass", "30log", "classic", "struct", "pack", "lbase64", "base64", "basexx", "xml2lua", "lxp", "lxp.lom",
  "xmlSimple", "windows", "win32", "winapi", "alien", "ex", "ps", "rings", "lpty", "linenoise", "readline", "lcomplex",
  "lmathx", "bc", "lrandom", "compat53", "compat53.module", "utf8", "lutf8lib", "lua-utf8", "iconv", "luaiconv", "ngx",
  "resty.core", "resty.string", "resty.http", "lunatest", "date", "luatz", "stdlib", "std", "luarocks.loader", "ltermbox",
  "lgi", "lua-cURL", "lzmq", "zmq", "redis", "mongo", "lpack", "tween", "vector", "lume", "luafun", "fun", "moses",
}
function P.search_path(name, path, sep)
  if type(path) ~= "string" or type(io) ~= "table" or type(io.open) ~= "function" then return nil end
  local fname = name:gsub("%.", (sep:gsub("%%", "%%%%")))
  local esc = fname:gsub("%%", "%%%%")
  for tmpl in path:gmatch("[^;]+") do
    local fn = tmpl:gsub("%?", esc)
    local ok, f = pcall(io.open, fn, "rb")
    if ok and f then f:close(); return fn end
  end
  return nil
end

local function mod_desc(m)
  if type(m) == "table" then
    local n = 0
    for _ in pairs(m) do n = n + 1 end
    local ver
    for _, k in ipairs { "_VERSION", "VERSION", "version", "_version" } do
      local ok, v = pcall(function() return m[k] end)
      if ok and (type(v) == "string" or type(v) == "number") then ver = tostring(v); break end
    end
    return "table(" .. n .. "项)" .. (ver and (" 版本 " .. ver) or "")
  end
  return type(m)
end

if OPT.modules then
  local sect = "模块"
  if type(package) == "table" then
    info(sect, "package.path", type(package.path) == "string" and (function()
      local t = {}
      for p in package.path:gmatch("[^;]+") do t[#t + 1] = p end
      return t
    end)() or nil)
    info(sect, "package.cpath", type(package.cpath) == "string" and (function()
      local t = {}
      for p in package.cpath:gmatch("[^;]+") do t[#t + 1] = p end
      return t
    end)() or nil)
    local sr = package.searchers or package.loaders
    info(sect, "searchers/loaders 数量", type(sr) == "table" and #sr or nil)
    if type(package.preload) == "table" then
      local t = {}
      for k in pairs(package.preload) do t[#t + 1] = tostring(k) end
      tsort(t)
      info(sect, "package.preload", #t > 0 and t or "空")
    end
  end
  local names = {}
  for k in pairs(LOADED0) do names[#names + 1] = tostring(k) end
  tsort(names)
  local builtin, third = {}, {}
  local BUILTIN = { _G = 1, string = 1, table = 1, math = 1, io = 1, os = 1, debug = 1, coroutine = 1, package = 1,
                    utf8 = 1, bit32 = 1, bit = 1, ffi = 1, jit = 1 }
  for _, k in ipairs(names) do
    local desc = k .. " = " .. mod_desc(LOADED0[k])
    if BUILTIN[k] or k:find("^jit%.") then builtin[#builtin + 1] = desc else third[#third + 1] = desc end
  end
  info(sect, "启动时已加载(内置库)", builtin)
  info(sect, "启动时已加载(其它/第三方/宿主)", #third > 0 and third or "无")

  -- 不执行 require,只按 package.path/cpath 查找文件是否存在
  local dirsep = type(package) == "table" and type(package.config) == "string" and package.config:sub(1, 1) or "/"
  local found, tried = {}, 0
  for _, name in ipairs(KNOWN_MODULES) do
    tried = tried + 1
    local state
    if LOADED0[name] ~= nil then state = nil
    elseif type(package) == "table" and type(package.preload) == "table" and package.preload[name] then state = "preload"
    else
      local f = P.search_path(name, type(package) == "table" and package.path, dirsep)
      if f then state = "lua: " .. f
      else
        local c = P.search_path(name, type(package) == "table" and package.cpath, dirsep)
        if not c and name:find("%.") then
          c = P.search_path(name:match("^[^.]+"), type(package) == "table" and package.cpath, dirsep)
          if c then c = c .. " (all-in-one 加载器)" end
        end
        if c then state = "C: " .. c end
      end
    end
    if state then found[#found + 1] = name .. "  ->  " .. state end
  end
  info(sect, "按路径可发现的常见模块 (探测 " .. tried .. " 个, 未执行 require)", #found > 0 and found or "无")
end

-- ---------------------------------------------------------------------------
-- 沙箱画像
-- ---------------------------------------------------------------------------
do
  local sect = "沙箱画像"
  local function has(p) return P.get(p) ~= nil end
  info(sect, "文件读写 io.open", has("io.open"))
  info(sect, "启动子进程 io.popen", has("io.popen"))
  info(sect, "执行命令 os.execute", has("os.execute"))
  info(sect, "退出进程 os.exit", has("os.exit"))
  info(sect, "环境变量 os.getenv", has("os.getenv"))
  info(sect, "动态加载代码 load/loadstring", P.rawload ~= nil)
  info(sect, "文件加载 loadfile/dofile", has("loadfile") and has("dofile"))
  info(sect, "字节码加载 (string.dump 回环)", D.dump and D.dump.roundtrip or false)
  info(sect, "C 模块加载 package.loadlib", has("package.loadlib"))
  info(sect, "require 可用", has("require"))
  info(sect, "debug 库", has("debug.getinfo"))
  info(sect, "debug.sethook", has("debug.sethook"))
  info(sect, "debug.getregistry", has("debug.getregistry"))
  info(sect, "collectgarbage", has("collectgarbage"))
  info(sect, "全局表可写", (pcall(function() G.__probe_w = 1; local v = G.__probe_w; G.__probe_w = nil; assert(v == 1) end)))
  local gm = getmetatable(G)
  info(sect, "_G 带元表 (严格模式/代理)", gm ~= nil)
  info(sect, "_G._G == _G", rawget(G, "_G") == G)
  if type(getfenv) == "function" then info(sect, "getfenv(0) == _G", (pcall(getfenv, 0)) and getfenv(0) == G or false) end
end

-- ---------------------------------------------------------------------------
-- 资源上限
-- ---------------------------------------------------------------------------
if OPT.limits then
  local sect = "资源上限"
  local function ge(n, cap) if n and cap and n >= cap then return ">= " .. n end return n end
  local function names(prefix, n) local t = {}; for i = 1, n do t[i] = prefix .. i end; return t end

  local ml = P.bsearch(1, 400, function(n) return P.syntax_ok("local " .. tconcat(names("a", n), ",")) end)
  info(sect, "单函数最大局部变量数", ge(ml, 400))

  local function up_ok(n)
    local k1 = math.min(n, 190); local k2 = n - k1
    local a, b, all = names("a", k1), names("b", k2), {}
    for i = 1, k1 do all[#all + 1] = a[i] end
    for i = 1, k2 do all[#all + 1] = b[i] end
    local src = "return function() local " .. tconcat(a, ",") .. "; return function() "
      .. (k2 > 0 and ("local " .. tconcat(b, ",") .. "; ") or "")
      .. "return function() return " .. tconcat(all, ",") .. " end end end"
    return P.syntax_ok(src)
  end
  info(sect, "单函数最大 upvalue 数", ge(P.bsearch(1, 380, up_ok), 380))

  local nest = P.bsearch(1, 1000, function(n) return P.syntax_ok("return " .. srep("(", n) .. "1" .. srep(")", n)) end)
  info(sect, "表达式括号最大嵌套", ge(nest, 1000))
  local tnest = P.bsearch(1, 1000, function(n) return P.syntax_ok("return " .. srep("{", n) .. srep("}", n)) end)
  info(sect, "table 构造器最大嵌套", ge(tnest, 1000))

  -- Lua 函数调用深度 (非尾调用)
  do
    local d, cap = 0, 400000
    local function f() d = d + 1; if d >= cap then return 0 end; return 1 + f() end
    local ok, e = pcall(f)
    info(sect, "Lua 递归深度上限", ge(d, cap))
    if not ok then info(sect, "栈溢出错误信息", P.strip_pos(e):sub(1, 90)) end
  end
  -- C 调用深度 (嵌套 pcall)
  do
    local d, cap = 0, 100000
    local function f() d = d + 1; if d >= cap then return end; pcall(f) end
    pcall(f)
    info(sect, "嵌套 pcall (C 栈) 深度上限", ge(d, cap))
  end
  -- unpack 返回值上限
  if unpack then
    local tbl = {}
    local cap = 1048576
    local u = P.bsearch(1, cap, function(n)
      local ok, c = pcall(function() return select("#", unpack(tbl, 1, n)) end)
      return ok and c == n
    end)
    info(sect, "unpack 单次最大返回值数", ge(u, cap))
  end
  -- 字符串/数字转换精度 (顺带)
  info(sect, "string.rep 1MB 可用", (pcall(string.rep, "x", 1048576)))
end

-- ---------------------------------------------------------------------------
-- 微基准
-- ---------------------------------------------------------------------------
if OPT.bench and type(os) == "table" and type(os.clock) == "function" then
  local sect = "基准"
  local BENCH = {
    { "整数加法循环 5e6", function() local s = 0; for i = 1, 5000000 do s = s + i end; return s end },
    { "浮点乘加循环 5e6", function() local x = 0.5; for i = 1, 5000000 do x = x * 1.0000001 + 0.1 end; return x end },
    { "函数调用 2e6", function() local function f(a) return a + 1 end; local s = 0; for _ = 1, 2000000 do s = f(s) end; return s end },
    { "表读写 1e6", function() local t = {}; for i = 1, 1000000 do t[i] = i end; local s = 0; for i = 1, 1000000 do s = s + t[i] end; return s end },
    { "string.format 2e5", function() local f = string.format; for i = 1, 200000 do local _ = f("%d:%s", i, "x") end end },
    { "字符串构造+concat 2e5", function() local t = {}; for i = 1, 200000 do t[#t + 1] = "k" .. i end; return tconcat(t) end },
    { "闭包创建 1e6", function() local f; for i = 1, 1000000 do f = function() return i end end; return f end },
  }
  local function timeit(f) local t = os.clock(); f(); return os.clock() - t end
  local jit = rawget(G, "jit")
  local jit_on = type(jit) == "table" and type(jit.off) == "function" and type(jit.on) == "function"
    and (select(1, pcall(jit.status)) and select(2, pcall(jit.status)))
  for _, b in ipairs(BENCH) do
    local t1 = timeit(b[2])
    local line = sfmt("%.0f ms", t1 * 1000)
    if jit_on then
      pcall(jit.off)
      if type(jit.flush) == "function" then pcall(jit.flush) end   -- 丢弃已编译的 trace,否则 off 后仍在跑机器码
      local t2 = timeit(b[2])
      pcall(jit.on)
      if type(jit.flush) == "function" then pcall(jit.flush) end
      line = line .. sfmt("  (jit.off: %.0f ms, 加速比 x%.1f)", t2 * 1000, t1 > 0 and t2 / t1 or 0)
    end
    info(sect, b[1], line)
  end
  info(sect, "说明", "耗时仅供同机横向对比;LuaJIT 的 jit.on/off 对比可直观看出 JIT 是否真的在工作")
end

-- ---------------------------------------------------------------------------
-- 判定 (summary)
-- ---------------------------------------------------------------------------
local function describe_dev(c, vi)
  local e = c.spec[vi]
  if e == "req" and not c.result then return "缺少该版本应有的特性" end
  return "出现了该版本不应有的特性"
end

do
  local S = D.summary
  S.probe = PROBE_VERSION
  S.implementation = IMPL.label
  S.version_string = rawget(G, "_VERSION")
  S.claimed = IMPL.claimed
  S.inferred = VERS[BEST]
  S.match_pct = SC[BEST].pct
  S.scores = {}
  for i = 1, #VERS do S.scores[VERS[i]] = { pct = SC[i].pct, deviations = #SC[i].bad, checks = SC[i].n } end

  local ext_features = {}
  if IMPL.base then
    for _, c in ipairs(SC[BEST].bad) do
      if c.result and c.spec[BEST] == nil then ext_features[#ext_features + 1] = c.group .. "." .. c.id end
    end
  end
  S.extensions_beyond_base = ext_features

  local compat_left = {}
  for _, c in ipairs(D.checks) do
    if not c.ext and c.result and c.spec[BEST] == "opt" then compat_left[#compat_left + 1] = c.group .. "." .. c.id end
  end
  S.compat_leftovers = compat_left

  local missing = {}
  for _, c in ipairs(D.checks) do
    if not c.ext and c.result == false and c.spec[BEST] == "req" then missing[#missing + 1] = c.group .. "." .. c.id end
  end
  S.missing_for_inferred = missing

  local dialects = {}
  for _, c in ipairs(D.checks) do if c.ext and c.result then dialects[#dialects + 1] = c.id end end
  S.dialect_features = dialects
end

-- ---------------------------------------------------------------------------
-- JSON
-- ---------------------------------------------------------------------------
local JMAP = { ['"'] = '\\"', ['\\'] = '\\\\', ['\n'] = '\\n', ['\r'] = '\\r', ['\t'] = '\\t' }
local function jstr(s)
  return '"' .. s:gsub('[%c"\\]', function(c) return JMAP[c] or sfmt("\\u%04x", c:byte()) end) .. '"'
end
local function to_json(v)
  local t = type(v)
  if t == "nil" then return "null"
  elseif t == "boolean" then return tostring(v)
  elseif t == "number" then
    if v ~= v or v == math.huge or v == -math.huge then return jstr(tostring(v)) end
    return tostring(v)
  elseif t == "string" then return jstr(v)
  elseif t == "table" then
    local cnt = 0
    for _ in pairs(v) do cnt = cnt + 1 end
    if cnt == 0 then return "[]" end
    if cnt == #v then
      local parts = {}
      for i = 1, #v do parts[i] = to_json(v[i]) end
      return "[" .. tconcat(parts, ",") .. "]"
    end
    local keys, m = {}, {}
    for k, val in pairs(v) do keys[#keys + 1] = tostring(k); m[tostring(k)] = val end
    tsort(keys)
    local parts = {}
    for i, k in ipairs(keys) do parts[i] = jstr(k) .. ":" .. to_json(m[k]) end
    return "{" .. tconcat(parts, ",") .. "}"
  end
  return jstr(tostring(v))
end

local function build_export()
  local J = { summary = D.summary, info = {}, checks = {} }
  for _, name in ipairs(D.order) do
    local o = {}
    for _, kv in ipairs(D.info[name]) do o[kv[1]] = kv[2] end
    J.info[name] = o
  end
  for _, c in ipairs(D.checks) do
    J.checks[#J.checks + 1] = { group = c.group, id = c.id, desc = c.desc, expect = c.expect, result = c.result, detail = c.detail }
  end
  return J
end

-- ---------------------------------------------------------------------------
-- 文本渲染
-- ---------------------------------------------------------------------------
local GROUP_NAME = {
  api = "API 存在性", syntax = "语法", numeric = "数值语义", string = "字符串库", table = "表 / 迭代",
  meta = "元表 / GC", coro = "协程", error = "错误处理", func = "函数 / 加载 / 调试", pkg = "模块系统",
  gc = "垃圾回收", os = "操作系统库", ext = "非标准扩展 / 方言 (不参与打分)",
}
local GROUP_ORDER = { "api", "syntax", "numeric", "string", "table", "meta", "coro", "error", "func", "pkg", "gc", "os", "ext" }

local function render()
  local L = {}
  local function w(s) L[#L + 1] = s end
  local bar = srep("=", 74)
  w(bar); w(" Lua 探针报告  (luaprobe " .. PROBE_VERSION .. ")"); w(bar)
  local S = D.summary
  w(sfmt(" 实现      : %s", tostring(S.implementation)))
  w(sfmt(" _VERSION   : %s", tostring(S.version_string)))
  if IMPL.base then
    w(sfmt(" 语义基线   : Lua %s   (特征匹配 %.1f%%)", S.inferred, S.match_pct))
  else
    w(sfmt(" 推断版本   : Lua %s   (特征匹配 %.1f%%)", S.inferred, S.match_pct))
    if S.claimed and S.claimed ~= S.inferred then
      w(sfmt(" !! 警告    : _VERSION 声明为 %s,但行为更接近 %s (可能被改写/裁剪/打了兼容补丁)", S.claimed, S.inferred))
    end
  end
  if #S.extensions_beyond_base > 0 then
    w(" 超出基线的扩展: " .. tconcat(S.extensions_beyond_base, ", "))
  end
  if #S.compat_leftovers > 0 then
    w(" 兼容层残留  : " .. tconcat(S.compat_leftovers, ", "))
  end
  if #S.missing_for_inferred > 0 then
    w(" 缺失的特性  : " .. tconcat(S.missing_for_inferred, ", "))
  end
  if #S.dialect_features > 0 then
    w(" 方言特征    : " .. tconcat(S.dialect_features, ", "))
  end
  w("")
  w(" 各版本匹配度 (特征 " .. tostring(SC[1].n) .. " 项):")
  for i = 1, #VERS do
    local mark = (i == BEST) and "  <== 判定" or ""
    w(sfmt("   Lua %s : %5.1f%%   偏差 %2d 项%s", VERS[i], SC[i].pct, #SC[i].bad, mark))
  end

  local function section(name)
    w(""); w("[" .. name .. "]")
    for _, kv in ipairs(D.info[name]) do
      local v = kv[2]
      if type(v) == "table" and #v > 1 then
        w("  " .. kv[1] .. " :")
        for _, item in ipairs(v) do w("      - " .. tostring(item)) end
      else
        w("  " .. kv[1] .. " : " .. P.fmtv(v))
      end
    end
  end
  for _, name in ipairs(D.order) do
    if not (OPT.brief and (name == "数值模型" or name == "模块" or name == "标准库" or name == "基准")) then
      section(name)
    end
  end

  w(""); w("[特性检测明细]   [+]=支持  [-]=不支持  *=与判定版本的预期不符")
  local byg = {}
  for _, c in ipairs(D.checks) do
    byg[c.group] = byg[c.group] or {}
    local t = byg[c.group]
    t[#t + 1] = c
  end
  for _, g in ipairs(GROUP_ORDER) do
    local list = byg[g]
    if list then
      local lines = {}
      for _, c in ipairs(list) do
        local dev = false
        if not c.ext and c.result ~= nil then
          local e = c.spec[BEST]
          if e == "req" and not c.result then dev = true end
          if e == nil and c.result then dev = true end
        end
        if not OPT.brief or dev then
          local mark = c.result == nil and "[?]" or (c.result and "[+]" or "[-]")
          lines[#lines + 1] = sfmt("   %s%s %-24s %-48s 期望:%s", dev and "*" or " ", mark, c.id, c.desc, c.expect)
        end
      end
      if #lines > 0 then
        w("  -- " .. (GROUP_NAME[g] or g))
        for _, l in ipairs(lines) do w(l) end
      end
    end
  end
  w(""); w("  [?] = 当前环境无法判定(例如库被裁剪),不计入打分")

  local bad = SC[BEST].bad
  if #bad > 0 then
    w(""); w("[与判定版本 Lua " .. VERS[BEST] .. " 不符的项]")
    for _, c in ipairs(bad) do
      w(sfmt("  - %s.%s : %s   (%s)", c.group, c.id, describe_dev(c, BEST), c.desc))
      if c.detail then w("      " .. tostring(c.detail)) end
    end
  end
  w(""); w(bar)
  return tconcat(L, "\n")
end

-- ---------------------------------------------------------------------------
-- 输出
-- ---------------------------------------------------------------------------
local TEXT = OPT.json and to_json(build_export()) or render()

if OPT.out and type(io) == "table" and type(io.open) == "function" then
  local f = io.open(OPT.out, "wb")
  if f then f:write(TEXT, "\n"); f:close() end
end
if not OPT.quiet then
  local pr = rawget(G, "print")
  if type(pr) == "function" then pr(TEXT)
  elseif type(io) == "table" and io.write then io.write(TEXT, "\n") end
end

return {
  text = TEXT,
  data = build_export(),
  json = function() return to_json(build_export()) end,
}
