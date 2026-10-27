module

public import CFSG.Certificates.Kernel.BabyMonster.FixSound
public import Certificates.Kernel.BabyMonster.Chain
public meta import Lean

public section

namespace CertificateChecks.KernelBM

open Lean Elab Tactic Meta

meta def checkLhsOf (nm : Name) : TacticM Expr := do
  let some ci := (← getEnv).find? nm | throwError "unknown check theorem {nm}"
  checkLhs ci.type

elab "bm_stripsn " p:ident n:num : tactic => withMainContext do
  let P := p.getId
  let n := n.getNat
  if n == 0 then throwError "bm_stripsn: no checks"
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for i in [0:n] do
    let b ← checkLhsOf (P.appendAfter s!"_{i}")
    let args := b.getAppArgs
    unless b.isAppOfArity ``Nat.beq 2 && args[0]!.isAppOfArity ``CFSG.KC.BM.mulWn 3 do
      throwError "bm_stripsn: {P}_{i} is not a check `Nat.beq (mulWn n Ws a) c = true`"
    parts := parts.push (args[0]!.appFn!.appArg!, args[0]!.appArg!, args[1]!)
  let Ws := parts[0]!.1
  let natE := mkConst ``Nat
  let mut acc := mkApp (mkConst ``CFSG.KC.BM.Fix.AllStripsN.nil) Ws
  let mut as := mkApp (mkConst ``List.nil [0]) natE
  let mut cs := mkApp (mkConst ``List.nil [0]) natE
  for i' in [0:n] do
    let i := n - 1 - i'
    let (_, a, c) := parts[i]!
    acc := mkAppN (mkConst ``CFSG.KC.BM.Fix.AllStripsN.cons)
      #[Ws, a, c, as, cs, mkConst (P.appendAfter s!"_{i}"), acc]
    as := mkApp3 (mkConst ``List.cons [0]) natE a as
    cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
  (← getMainGoal).assign acc
  replaceMainGoal []

elab "bm_blocksn " p:ident n:num : tactic => withMainContext do
  let P := p.getId
  let n := n.getNat
  let natE := mkConst ``Nat
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for i in [0:n] do
    let b ← checkLhsOf (P.appendAfter s!"_{i}")
    unless b.isAppOfArity ``CFSG.KC.BM.blockOKn 4 do
      throwError "bm_blocksn: {P}_{i} is not a check `blockOKn n blk T s = true`"
    let args := b.getAppArgs
    unless args[3]!.rawNatLit? == some i do
      throwError "bm_blocksn: {P}_{i} checks block {args[3]!}"
    parts := parts.push (args[1]!, args[2]!, args[3]!)
  let mut acc := mkApp (mkConst ``CFSG.KC.BM.Fix.AllBlocksN.nil)
    (mkApp (mkConst ``Nat.succ) (mkRawNatLit (n - 1)))
  let mut R := mkApp (mkConst ``List.nil [0]) natListE
  let mut S := mkApp (mkConst ``List.nil [0]) natE
  for i' in [0:n] do
    let i := n - 1 - i'
    let (blk, T, s) := parts[i]!
    acc := mkAppN (mkConst ``CFSG.KC.BM.Fix.AllBlocksN.cons)
      #[blk, T, s, R, S, mkConst (P.appendAfter s!"_{i}"), acc]
    R := mkApp3 (mkConst ``List.cons [0]) natListE blk R
    S := mkApp3 (mkConst ``List.cons [0]) natE T S
  (← getMainGoal).assign acc
  replaceMainGoal []

elab "bm_stripsx " p:ident n:num : tactic => withMainContext do
  let P := p.getId
  let n := n.getNat
  if n == 0 then throwError "bm_stripsx: no checks"
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for i in [0:n] do
    let b ← checkLhsOf (P.appendAfter s!"{i}")
    let args := b.getAppArgs
    unless b.isAppOfArity ``Nat.beq 2 && args[0]!.isAppOfArity ``Nat.xor 2 &&
        args[0]!.appFn!.appArg!.isAppOfArity ``CFSG.KC.BM.mulS 2 do
      throwError "bm_stripsx: {P}{i} is not a check `Nat.beq (Nat.xor (mulS Q a) a) c = true`"
    let m := args[0]!.appFn!.appArg!
    parts := parts.push (m.appFn!.appArg!, m.appArg!, args[1]!)
  let Q := parts[0]!.1
  let natE := mkConst ``Nat
  let mut acc := mkApp (mkConst ``CFSG.KC.BM.Fix.AllStripsX.nil) Q
  let mut as := mkApp (mkConst ``List.nil [0]) natE
  let mut cs := mkApp (mkConst ``List.nil [0]) natE
  for i' in [0:n] do
    let i := n - 1 - i'
    let (_, a, c) := parts[i]!
    acc := mkAppN (mkConst ``CFSG.KC.BM.Fix.AllStripsX.cons)
      #[Q, a, c, as, cs, mkConst (P.appendAfter s!"{i}"), acc]
    as := mkApp3 (mkConst ``List.cons [0]) natE a as
    cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
  (← getMainGoal).assign acc
  replaceMainGoal []

end CertificateChecks.KernelBM

end
