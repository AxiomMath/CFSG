module

public import CFSG.Certificates.Kernel.BabyMonster.Sound
public meta import Lean

public section

namespace CertificateChecks.KernelBM

open Lean Elab Tactic Meta

syntax "bm_chain " "[" ident,* "]" ident num term:max "[" ident,* "]" (" with " ident)? : tactic

elab_rules : tactic
  | `(tactic| bm_chain [$ls,*] $c $n $start [$ms,*] $[with $tab]?) => withMainContext do
  let Ls ← ls.getElems.mapM fun i => (realizeGlobalConstNoOverloadWithInfo i : TacticM Name)
  let Ms ← ms.getElems.mapM fun i => (realizeGlobalConstNoOverloadWithInfo i : TacticM Name)
  let mut rest : Option Expr := none
  if let some t := tab then
    let T ← realizeGlobalConstNoOverloadWithInfo t
    let some v := (← getConstInfo T).value? | throwError "bm_chain: {T} has no value"
    rest := some (← zetaReduce v)
  let C := c.getId
  let listE := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)
  let hok := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
  let mut acc ← Term.elabTerm start none
  Term.synthesizeSyntheticMVarsNoPostponing
  acc ← instantiateMVars acc
  for s in [0:n.getNat] do
    let nm := C.appendAfter s!"{s}"
    let some ci := (← getEnv).find? nm | throwError "bm_chain: unknown check {nm}"
    let some (_, b, _) := ci.type.eq? | throwError "bm_chain: {nm} is not `b = true`"
    unless b.isAppOfArity ``Nat.beq 2 do throwError "bm_chain: {nm} is not `Nat.beq T R = true`"
    let R := b.appArg!
    let mut e := b.appFn!.appArg!
    let mut mv : Array (Expr × Expr × Nat) := #[]
    while e.isAppOfArity ``Nat.lor 2 do
      let x := e.appArg!
      unless x.isAppOfArity ``CFSG.KC.BM.mulS 2 do throwError "bm_chain: {nm}: bad move {x}"
      let B := x.appFn!.appArg!
      let some i := Ms.findIdx? (B.isConstOf ·) | throwError "bm_chain: {nm}: unknown matrix {B}"
      mv := mv.push (B, x.appArg!.appArg!.appArg!, i)
      e := e.appFn!.appArg!
    unless e.isAppOfArity ``Nat.sub 2 do throwError "bm_chain: {nm}: bad base {e}"
    let P := e.appFn!.appArg!
    let U := e.appArg!.appArg!.appArg!
    mv := mv.reverse
    let some L := Ls[mv.size - 1]? | throwError "bm_chain: {nm}: no lemma for {mv.size} moves"
    let mut args := #[mkNatLit s, P, R, U]
    for (B, m, i) in mv do
      args := args ++ #[B, m, mkNatLit i]
    if let some r := rest then
      unless r.isAppOfArity ``List.cons 3 do
        throwError "bm_chain: the table ends at step {s}"
      args := args ++ #[r.appFn!.appArg!, r.appArg!]
      rest := some r.appArg!
    args := args.push (mkConst nm)
    for (B, _, _) in mv do
      args := args.push (mkApp2 (mkConst ``Eq.refl [Level.one]) listE B)
    acc := mkAppN (mkConst L) (args.push hok |>.push acc)
  (← getMainGoal).assign acc
  replaceMainGoal []

end CertificateChecks.KernelBM

end
