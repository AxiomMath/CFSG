module

public import Init
public meta import Lean
public import Lean.Exception

public section

namespace CertificateChecks.KernelBM

theorem forallLt_zero {P : Nat → Prop} : ∀ s < 0, P s := fun s h => absurd h (Nat.not_lt_zero s)

theorem forallLt_succ {P : Nat → Prop} {n : Nat} (h : ∀ s < n, P s) (hn : P n) :
    ∀ s < n + 1, P s := fun s hs =>
  (Nat.lt_succ_iff_lt_or_eq.1 hs).elim (h s) (fun e => e ▸ hn)

open Lean Elab Tactic Meta

elab "forall_lt_consts " p:ident n:num : tactic => withMainContext do
  let T := p.getId
  let n := n.getNat
  let g ← getMainGoal
  let P ← forallBoundedTelescope (← g.getType) (some 2) fun xs body => do
    unless xs.size == 2 do throwError "forall_lt_consts: the goal is not `∀ s < n, P s`"
    mkLambdaFVars #[xs[0]!] body
  let mut acc := mkApp (mkConst ``forallLt_zero) P
  for i in [0:n] do
    let nm := T.appendAfter s!"{i}"
    unless (← getEnv).contains nm do throwError "unknown theorem {nm}"
    acc := mkAppN (mkConst ``forallLt_succ) #[P, mkRawNatLit i, acc, mkConst nm]
  g.assign acc
  replaceMainGoal []

end CertificateChecks.KernelBM

end
