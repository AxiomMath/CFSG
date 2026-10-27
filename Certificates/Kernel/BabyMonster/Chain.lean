module

public import CFSG.Certificates.Kernel.BabyMonster.Sound
public meta import Lean

public section

namespace CertificateChecks.KernelBM

open Lean Elab Tactic Meta

meta def checkType (P : Name) (i : Nat) : TacticM Expr := do
  let nm := P.appendAfter s!"_{i}"
  let some ci := (← getEnv).find? nm | throwError "unknown check theorem {nm}"
  return ci.type

meta def checkLhs (t : Expr) : TacticM Expr := do
  let some (_, b, _) := t.eq? | throwError "not a check `b = true`:{indentExpr t}"
  return b

meta def natListE : Expr := mkApp (mkConst ``List [0]) (mkConst ``Nat)

elab "bm_strips " p:ident n:num : tactic => withMainContext do
  let P := p.getId
  let n := n.getNat
  if n == 0 then throwError "bm_strips: no checks"
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for i in [0:n] do
    let b ← checkLhs (← checkType P i)
    let args := b.getAppArgs
    unless b.isAppOfArity ``Nat.beq 2 && args[0]!.isAppOfArity ``CFSG.KC.BM.mulW 2 do
      throwError "bm_strips: {P}_{i} is not a check `Nat.beq (mulW Ws a) c = true`"
    parts := parts.push (args[0]!.appFn!.appArg!, args[0]!.appArg!, args[1]!)
  let Ws := parts[0]!.1
  let natE := mkConst ``Nat
  let mut acc := mkApp (mkConst ``CFSG.KC.BM.AllStrips.nil) Ws
  let mut as := mkApp (mkConst ``List.nil [0]) natE
  let mut cs := mkApp (mkConst ``List.nil [0]) natE
  for i' in [0:n] do
    let i := n - 1 - i'
    let (_, a, c) := parts[i]!
    acc := mkAppN (mkConst ``CFSG.KC.BM.AllStrips.cons)
      #[Ws, a, c, as, cs, mkConst (P.appendAfter s!"_{i}"), acc]
    as := mkApp3 (mkConst ``List.cons [0]) natE a as
    cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
  (← getMainGoal).assign acc
  replaceMainGoal []

elab "bm_blocks " p:ident n:num : tactic => withMainContext do
  let P := p.getId
  let n := n.getNat
  let natE := mkConst ``Nat
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for i in [0:n] do
    let b ← checkLhs (← checkType P i)
    unless b.isAppOfArity ``CFSG.KC.BM.blockOK 3 do
      throwError "bm_blocks: {P}_{i} is not a check `blockOK blk T s = true`"
    let args := b.getAppArgs
    unless args[2]!.rawNatLit? == some i do
      throwError "bm_blocks: {P}_{i} checks block {args[2]!}"
    parts := parts.push (args[0]!, args[1]!, args[2]!)
  let mut acc := mkApp (mkConst ``CFSG.KC.BM.AllBlocks.nil)
    (mkApp (mkConst ``Nat.succ) (mkRawNatLit (n - 1)))
  let mut R := mkApp (mkConst ``List.nil [0]) natListE
  let mut S := mkApp (mkConst ``List.nil [0]) natE
  for i' in [0:n] do
    let i := n - 1 - i'
    let (blk, T, s) := parts[i]!
    acc := mkAppN (mkConst ``CFSG.KC.BM.AllBlocks.cons)
      #[blk, T, s, R, S, mkConst (P.appendAfter s!"_{i}"), acc]
    R := mkApp3 (mkConst ``List.cons [0]) natListE blk R
    S := mkApp3 (mkConst ``List.cons [0]) natE T S
  (← getMainGoal).assign acc
  replaceMainGoal []

end CertificateChecks.KernelBM

end
