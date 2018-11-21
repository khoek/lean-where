reserve prefix `#where`:max

open lean.parser tactic
open interactive

namespace command.where

meta def sanitize_prefix (pfx : name) : name → name
| name.anonymous := name.anonymous
| (name.mk_string s p) :=
  if p.get_prefix.get_prefix = name.anonymous then name.mk_string s pfx
  else name.mk_string s name.anonymous
| (name.mk_numeral s p) :=
  let s := "n" ++ to_string s in
  if p.get_prefix.get_prefix = name.anonymous then name.mk_string s pfx
  else name.mk_string s name.anonymous

meta def mk_user_fresh_name : tactic name := do
  nm ← mk_fresh_name,
  return $ (sanitize_prefix `user__ nm).append `user

meta def mk_flag (let_conts : option name := none) : lean.parser name := do
  n ← mk_user_fresh_name,
  (_, s) ← match let_conts with
  | none := with_input command_like sformat!"def {n} : unit := ()"
  | some v := with_input command_like sformat!"def {n} : unit := let {v} := {v} in ()"
  end,
  resolve_constant n

meta def get_namespace (flag : name) : lean.parser name := do
  return $ flag.get_prefix.get_prefix.get_prefix

meta def trace_namespace (ns : name) : lean.parser unit := do
  let str := match ns with
  | name.anonymous := "[root namespace]"
  | ns := to_string ns
  end,
  tactic.trace format!"namespace: {str}"

meta def strip_binders : expr → list (name × binder_info × expr)
| (expr.pi n bi t b) := (n, bi, t) :: strip_binders b
| _ := []

meta def get_includes (flag : name) : tactic (list (name × binder_info × expr)) :=
  strip_binders <$> (mk_const flag >>= infer_type)

meta def binder_brackets : binder_info → string × string
| binder_info.implicit        := ("{", "}")
| binder_info.strict_implicit := ("{", "}")
| binder_info.inst_implicit   := ("[", "]")
| _                           := ("(", ")")

meta def format_binder : name × binder_info × expr → tactic string
| (n, bi, e) := do
  let (l, r) := binder_brackets bi,
  e ← pp e,
  return sformat!"{l}{n} : {e}{r}"

meta def format_variable_list (l : list (name × binder_info × expr)) : tactic string := do
  string.intercalate "" <$> l.mmap format_binder

meta def trace_includes (flag : name) : lean.parser unit := do
  l ← get_includes flag,
  str ← format_variable_list l,
  if l.length = 0 then skip
  else tactic.trace format!"includes:  {str}"

meta def get_all_in_namespace (ns : name) : tactic (list name) := do
  e ← get_env,
  return $ e.fold [] $ λ d l,
    if ns.is_prefix_of d.to_name then d.to_name :: l else l

meta def erase_duplicates {α : Type} [decidable_eq α] : list α → list α
| [] := []
| (x :: t) := (x :: erase_duplicates (t.filter $ λ a, a ≠ x))

meta def fetch_potential_variable_names (ns : name) : tactic (list (name × binder_info × expr)) := do
  l ← get_all_in_namespace ns,
  l ← l.mmap (λ n, do
    t ← mk_const n >>= infer_type, return $strip_binders t),
  return $ erase_duplicates l.join

meta def is_variable_name : name × binder_info × expr → lean.parser bool
| (n, bi, e) :=
  (mk_flag n >> return tt) <|> return ff

meta def trace_variables (ns : name) : lean.parser unit := do
  l ← fetch_potential_variable_names ns,
  l ← l.mfilter is_variable_name,
  str ← format_variable_list l,
  if l.length = 0 then skip
  else tactic.trace format!"variables: {str}"

meta def trace_where : lean.parser unit := do
  f ← mk_flag,
  ns ← get_namespace f,
  trace_namespace ns,
  trace_includes f,
  trace_variables ns

@[user_command]
meta def where_cmd (_ : decl_meta_info) (_ : parse $ tk "#where") : lean.parser unit := trace_where

end command.where
