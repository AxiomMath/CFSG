module

public meta import Lean
public import Lean.Exception

public meta section
open Lean Meta Elab Term

def yardstonePropositionType (proposition : Expr) : MetaM Expr := do
  forallTelescope (← inferType proposition) fun arguments result => do
    unless ← isDefEq result (.sort .zero) do
      throwError "Yardstone target must name a proposition-valued declaration"
    mkForallFVars arguments (mkAppN proposition arguments)

syntax "yardstone_type% " ident : term
elab_rules : term
  | `(yardstone_type% $name:ident) => withoutExporting do
      yardstonePropositionType (← mkConstWithFreshMVarLevels name.getId)
