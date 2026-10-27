module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3Co1Inputs
public import CFSG.Sporadic.Co1.Module.InvGroupBase
public import CFSG.Sporadic.Co1.Module.OddBuildBase
public import CFSG.Sporadic.Co1.Module.OddChecksBase
public import CFSG.Sporadic.Co1.Module.OddFactsBase
public import CFSG.Sporadic.Co1.Module.OddLit
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec

public section

namespace CFSG.EvenSporadicStandard.TwoB.MW3

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Odd CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative

@[expose] def unpackRK (d M : ℕ) : Array ℕ := Array.ofFn (n := d) fun i => M / 2 ^ (d * i.val) % 2 ^ d

@[expose] def rrOn (regs : Array (Array ℕ)) (i : ℕ) : Array ℕ := regs[i]?.getD (idRows 24)

@[expose] def sumRowsOn (regs : Array (Array ℕ)) (l : List ℕ) : Array ℕ :=
  l.foldl (fun acc i => addRows acc (rrOn regs i)) (Array.replicate 24 0)

@[expose] def sRowsOn (regs : Array (Array ℕ)) : Array ℕ :=
  (cycIdx.map fun i => actRows (rrOn regs i) vec0).toArray

@[expose] def eRowsOn (r : Array ℕ) : Array ℕ := Array.ofFn (n := 24) fun i =>
  (if vec0.testBit i then coef1 else 0) ^^^ (if (actRows r vec0).testBit i then coef2 else 0)

@[expose] def commOKOn (regs : Array (Array ℕ)) (r : Array ℕ) : Bool :=
  (cycIdx ++ relIdx).all (fun i => mulRows 24 (rrOn regs i) r == mulRows 24 r (rrOn regs i)) &&
    (mulRows 24 (transposeRows 24 (sRowsOn regs)) sInvRows == idRows 24) &&
    (actRows (sumRowsOn regs relIdx) vec0 == 0) &&
    (addRows (mulRows 24 cRows (sumRowsOn regs relIdx)) (idRows 24) == eRowsOn r)

theorem commOK_eq_on : commOK = commOKOn regsRowsM (rr 27) := rfl

end CFSG.EvenSporadicStandard.TwoB.MW3

end
