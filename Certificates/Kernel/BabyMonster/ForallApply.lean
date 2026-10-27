module

public import Certificates.Kernel.BabyMonster.ForallLt
public import CFSG.Certificates.Kernel.BabyMonster.F2
public meta import Lean

public section

namespace CertificateChecks.KernelBM

open Lean Elab Tactic Meta

elab "forall_lt_vecmul " p:ident q:ident n:num l:ident : tactic => withMainContext do
  let T := p.getId
  let U := q.getId
  let n := n.getNat
  let L ← realizeGlobalConstNoOverload l
  let g ← getMainGoal
  let P ← forallBoundedTelescope (← instantiateMVars (← g.getType)) (some 2) fun xs body => do
    unless xs.size == 2 do throwError "forall_lt_vecmul: the goal is not `∀ s < n, P s`"
    mkLambdaFVars #[xs[0]!] body
  let natL := mkApp (mkConst ``List [0]) (mkApp (mkConst ``List [0]) (mkConst ``Nat))
  let mut acc := mkApp (mkConst ``forallLt_zero) P
  for i in [0:n] do
    let nm := T.appendAfter s!"{i}"
    let um := U.appendAfter s!"{i}"
    let some ci := (← getEnv).find? nm | throwError "unknown theorem {nm}"
    unless (← getEnv).contains um do throwError "unknown theorem {um}"
    let chk := ci.type.appFn!.appArg!
    let vm := chk.appFn!.appArg!
    unless vm.isAppOfArity ``CFSG.KC.BM.vecMul 2 do throwError "{nm}: not a `vecMul` check"
    let C := vm.appFn!.appArg!
    let refl := mkApp2 (mkConst ``Eq.refl [Level.one]) natL C
    let pf := mkAppN (mkConst L) #[mkRawNatLit i, C, mkConst nm, mkConst um, refl]
    acc := mkAppN (mkConst ``forallLt_succ) #[P, mkRawNatLit i, acc, pf]
  g.assign acc
  replaceMainGoal []

end CertificateChecks.KernelBM

end
