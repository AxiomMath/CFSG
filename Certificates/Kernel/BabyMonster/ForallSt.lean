module

public import Certificates.Kernel.BabyMonster.ForallLt
public import CFSG.Certificates.Kernel.BabyMonster.DyStab
public meta import Lean
public import CFSG.Certificates.Kernel.BabyMonster.PktTab
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

public section

namespace CertificateChecks.KernelBM

open Lean Elab Tactic Meta

meta def forallLtPred (g : MVarId) : MetaM Expr := do
  forallBoundedTelescope (← instantiateMVars (← g.getType)) (some 2) fun xs body => do
    unless xs.size == 2 do throwError "the goal is not `∀ s < n, P s`"
    mkLambdaFVars #[xs[0]!] body

elab "forall_lt_st " p:ident n:num : tactic => withMainContext do
  let T := p.getId
  let n := n.getNat
  let g ← getMainGoal
  let P ← forallLtPred g
  let body := P.bindingBody!
  let lhs := body.appFn!.appArg!
  unless lhs.isAppOfArity ``CFSG.KC.BM.Dy.stOK 4 do throwError "the goal is not about `stOK`"
  let gargs := lhs.getAppArgs
  let mut acc := mkApp (mkConst ``forallLt_zero) P
  for i in [0:n] do
    let nm := T.appendAfter s!"{i}"
    let some ci := (← getEnv).find? nm | throwError "unknown theorem {nm}"
    let chk := ci.type.appFn!.appArg!
    let W := chk.appArg!
    let V := chk.appFn!.appArg!.appArg!
    let refl (e : Expr) := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) e
    let pf := mkAppN (mkConst ``CFSG.KC.BM.Dy.stOK_of)
      #[gargs[0]!, gargs[1]!, gargs[2]!, mkRawNatLit i, V, W, mkConst nm, refl V, refl W]
    acc := mkAppN (mkConst ``forallLt_succ) #[P, mkRawNatLit i, acc, pf]
  g.assign acc
  replaceMainGoal []

elab "forall_lt_cols " p:ident n:num : tactic => withMainContext do
  let T := p.getId
  let n := n.getNat
  let g ← getMainGoal
  let P ← forallLtPred g
  let mut acc := mkApp (mkConst ``forallLt_zero) P
  for m in [0:n] do
    let nm := T.appendAfter s!"{m / 4}_{16 * (m % 4)}"
    unless (← getEnv).contains nm do throwError "unknown theorem {nm}"
    acc := mkAppN (mkConst ``forallLt_succ) #[P, mkRawNatLit m, acc, mkConst nm]
  g.assign acc
  replaceMainGoal []

end CertificateChecks.KernelBM

end
