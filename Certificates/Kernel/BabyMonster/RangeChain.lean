module

public import CFSG.Certificates.Kernel.BabyMonster.CensusSound
public meta import Lean
public import Lean.Exception

public section

namespace CertificateChecks.KernelBM

open Lean Elab Tactic Meta

elab "bm_ranges " h:ident p:ident n:num : tactic => withMainContext do
  let P := p.getId
  let n := n.getNat
  if n == 0 then throwError "bm_ranges: no checks"
  let natE := mkConst ``Nat
  let mut parts : Array (Array Expr × Expr) := #[]
  for i in [0:n] do
    let nm := P.appendAfter s!"{i}"
    let some ci := (← getEnv).find? nm | throwError "unknown check theorem {nm}"
    let some (_, b, _) := ci.type.eq? | throwError "{nm}: not a check `b = true`"
    let args := b.getAppArgs
    unless b.isAppOfArity ``Nat.beq 2 && args[0]!.isAppOfArity ``CFSG.KC.BM.censusRange 7 do
      throwError "bm_ranges: {nm} is not a range check"
    parts := parts.push (args[0]!.getAppArgs, args[1]!)
  let base := parts[0]!.1
  let (LB, DT, Ts, reps, len, cnt) := (base[0]!, base[1]!, base[2]!, base[3]!, base[5]!, base[6]!)
  for (rargs, _) in parts do
    unless rargs[5]! == len && rargs[6]! == cnt do
      throwError "bm_ranges: the checks differ in length or initial count"
  let some lastLo := parts[n - 1]!.1[4]!.rawNatLit? | throwError "bm_ranges: bound not a literal"
  let some lenN := len.rawNatLit? | throwError "bm_ranges: length not a literal"
  let hi := mkRawNatLit (lastLo + lenN)
  let pre := #[LB, DT, Ts, reps, len, cnt]
  let mut acc := mkAppN (mkConst ``CFSG.KC.BM.AllRanges.nil) (pre.push hi)
  let mut cs := mkApp (mkConst ``List.nil [0]) natE
  for i' in [0:n] do
    let i := n - 1 - i'
    let (rargs, c) := parts[i]!
    acc := mkAppN (mkConst ``CFSG.KC.BM.AllRanges.cons)
      (pre ++ #[c, rargs[4]!, hi, cs, mkConst (P.appendAfter s!"{i}"), acc])
    cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
  let lo := parts[0]!.1[4]!
  let ty := mkAppN (mkConst ``CFSG.KC.BM.AllRanges) (pre ++ #[cs, lo, hi])
  let g ← (← getMainGoal).assert h.getId ty acc
  let (_, g) ← g.intro1P
  replaceMainGoal [g]

end CertificateChecks.KernelBM

end
