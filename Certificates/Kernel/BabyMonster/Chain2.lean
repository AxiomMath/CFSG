module

public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import Certificates.Kernel.BabyMonster.Chain
public meta import Lean

public section

namespace CertificateChecks.KernelBM

open Lean Elab Tactic Meta

elab "bm_strips2 " p:ident n:num : tactic => withMainContext do
  let P := p.getId
  let n := n.getNat
  if n == 0 then throwError "bm_strips2: no checks"
  let mut parts : Array (Expr × Expr × Expr × Expr) := #[]
  for i in [0:n] do
    let b ← checkLhs (← checkType P i)
    let args := b.getAppArgs
    unless b.isAppOfArity ``Nat.beq 2 && args[0]!.isAppOfArity ``CFSG.KC.BM.mulW 2 &&
        args[1]!.isAppOfArity ``CFSG.KC.BM.mulW 2 do
      throwError "bm_strips2: {P}_{i} is not a check `Nat.beq (mulW Ws a) (mulW Ds c) = true`"
    parts := parts.push (args[0]!.appFn!.appArg!, args[0]!.appArg!, args[1]!.appFn!.appArg!,
      args[1]!.appArg!)
  let (Ws, _, Ds, _) := parts[0]!
  let natE := mkConst ``Nat
  let mut acc := mkApp2 (mkConst ``CFSG.KC.BM.AllStrips2.nil) Ws Ds
  let mut as := mkApp (mkConst ``List.nil [0]) natE
  let mut cs := mkApp (mkConst ``List.nil [0]) natE
  for i' in [0:n] do
    let i := n - 1 - i'
    let (_, a, _, c) := parts[i]!
    acc := mkAppN (mkConst ``CFSG.KC.BM.AllStrips2.cons)
      #[Ws, Ds, a, c, as, cs, mkConst (P.appendAfter s!"_{i}"), acc]
    as := mkApp3 (mkConst ``List.cons [0]) natE a as
    cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
  (← getMainGoal).assign acc
  replaceMainGoal []

meta def stepParts (F : Name) : TacticM (Expr × Array Expr × Name) := do
  let mut as : Array Expr := #[]
  let mut Ws : Expr := default
  let mut M : Name := .anonymous
  for j in [0:69] do
    let b ← checkLhs (← checkType F j)
    let args := b.getAppArgs
    unless b.isAppOfArity ``Nat.beq 2 && args[0]!.isAppOfArity ``CFSG.KC.BM.mulW 2 do
      throwError "bm_wchain: {F}_{j} is not a check `Nat.beq (mulW Ws a) c = true`"
    if j == 0 then
      Ws := args[0]!.appFn!.appArg!
      let c := args[1]!
      let c := if c.isAppOfArity ``CFSG.KC.BM.mulW 2 then c.appArg! else c
      let some nm := c.constName? | throwError "bm_wchain: {F}_0 has no constant target strip"
      M := nm.getPrefix
    as := as.push args[0]!.appArg!
  return (Ws, as, M)

elab "bm_wchain " p:ident n:num w:ident : tactic => withMainContext do
  let P := p.getId
  let n := n.getNat
  let W := w.getId
  let natE := mkConst ``Nat
  let natListE := mkApp (mkConst ``List [0]) natE
  let listOf (xs : Array Expr) : Expr :=
    xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natE x acc)
      (mkApp (mkConst ``List.nil [0]) natE)
  let fams := (Array.range n).map (fun i => P.appendAfter s!"_{i}") |>.push P
  let mut steps : Array (Expr × Expr × Name) := #[]
  for F in fams do
    let (Ws, as, M) ← stepParts F
    steps := steps.push (Ws, listOf as, M)
  let lastC := mkConst steps.back!.2.2
  let mut acc := mkApp (mkConst ``CFSG.KC.BM.WChain.nil) lastC
  let mut Fs := mkApp (mkConst ``List.nil [0]) natListE
  for k' in [0:steps.size] do
    let k := steps.size - 1 - k'
    let (Ws, A, M) := steps[k]!
    let F := fams[k]!
    let mut hs := mkApp (mkConst ``CFSG.KC.BM.AllStrips.nil) Ws
    let mut as := mkApp (mkConst ``List.nil [0]) natE
    let mut cs := mkApp (mkConst ``List.nil [0]) natE
    for j' in [0:69] do
      let j := 68 - j'
      let b ← checkLhs (← checkType F j)
      let args := b.getAppArgs
      let a := args[0]!.appArg!
      let c := args[1]!
      hs := mkAppN (mkConst ``CFSG.KC.BM.AllStrips.cons)
        #[Ws, a, c, as, cs, mkConst (F.appendAfter s!"_{j}"), hs]
      as := mkApp3 (mkConst ``List.cons [0]) natE a as
      cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
    let B := mkConst M
    let wfB := mkConst (W.appendAfter M.getString!)
    acc := mkAppN (mkConst ``CFSG.KC.BM.WChain.step) #[Ws, Fs, A, B, lastC, hs, wfB, acc]
    Fs ← mkAppM ``HAppend.hAppend #[Ws, Fs]
  (← getMainGoal).assign acc
  replaceMainGoal []

end CertificateChecks.KernelBM

end
