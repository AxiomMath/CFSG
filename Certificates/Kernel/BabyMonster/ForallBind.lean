module

public import Certificates.Kernel.BabyMonster.ForallSt
public meta import Lean

public section

namespace CertificateChecks.KernelBM

open Lean Elab Tactic Meta

meta partial def structMatch (p t : Expr) : MetaM Bool := do
  let p ← instantiateMVars p
  if p.isMVar then
    let m := p.mvarId!
    if !(← m.isAssigned) then
      m.assign t
      return true
  match p, t with
  | .app f a, .app g b => return (← structMatch f g) && (← structMatch a b)
  | .mdata _ p', _ => structMatch p' t
  | _, .mdata _ t' => structMatch p t'
  | _, _ => return p == t

meta def bindProof (L T : Name) (i : Option Nat) : MetaM Expr := do
  let some ci := (← getEnv).find? T | throwError "unknown theorem {T}"
  let chk := ci.type
  let e0 := mkConst L ((← getConstInfo L).levelParams.map fun _ => Level.zero)
  let e := match i with
    | some k => mkApp e0 (mkRawNatLit k)
    | none => e0
  let (ms, _, _) ← forallMetaTelescope (← inferType e)
  let mut found := false
  for m in ms do
    let ty ← instantiateMVars (← inferType m)
    if !found && ty.isAppOfArity ``Eq 3 && ty.appFn!.appFn!.appArg!.isConstOf ``Bool then
      unless ← structMatch ty chk do throwError "bm_bind: {T} does not match the check of {L}"
      m.mvarId!.assign (mkConst T)
      found := true
  unless found do throwError "bm_bind: {L} has no check hypothesis"
  for m in ms do
    if !(← m.mvarId!.isAssigned) then
      let ty ← instantiateMVars (← inferType m)
      unless ty.isAppOfArity ``Eq 3 do throwError "bm_bind: unassigned part of {L}"
      let lvl := match ty.getAppFn with
        | .const _ [u] => u
        | _ => Level.one
      m.mvarId!.assign (mkApp2 (mkConst ``Eq.refl [lvl]) ty.appFn!.appFn!.appArg!
        ty.appFn!.appArg!)
  instantiateMVars (mkAppN e ms)

elab "bm_bind " l:ident t:ident : tactic => withMainContext do
  let L ← realizeGlobalConstNoOverloadWithInfo l
  let pf ← bindProof L t.getId none
  (← getMainGoal).assign pf
  replaceMainGoal []

elab "forall_lt_bind " t:ident n:num l:ident : tactic => withMainContext do
  let T := t.getId
  let L ← realizeGlobalConstNoOverloadWithInfo l
  let g ← getMainGoal
  let P ← forallLtPred g
  let mut acc := mkApp (mkConst ``forallLt_zero) P
  for i in [0:n.getNat] do
    let pf ← bindProof L (T.appendAfter s!"{i}") (some i)
    acc := mkAppN (mkConst ``forallLt_succ) #[P, mkRawNatLit i, acc, pf]
  g.assign acc
  replaceMainGoal []

end CertificateChecks.KernelBM

end
