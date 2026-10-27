module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvConjData

public section

namespace CFSG.KC.TransvK

open CFSG.EvenSporadicStandard.ThStd.LocalDataTh

@[expose] def appK (a b c d v : ℕ) : ℕ :=
  let s0 := if v.testBit 0 then 0 ^^^ a else 0
  let s1 := if v.testBit 1 then s0 ^^^ b else s0
  let s2 := if v.testBit 2 then s1 ^^^ c else s1
  if v.testBit 3 then s2 ^^^ d else s2

@[expose] def fixedCountK (a b c d : ℕ) : ℕ :=
  ((List.range 16).filter fun v => Nat.beq (appK a b c d v) v).length

@[expose] def tLeafK (a b c d : ℕ) : Bool :=
  !(decide (8 ≤ fixedCountK a b c d) && [a, b, c, d] != idCols 4 && invCode [a, b, c, d]) ||
    convTab.any fun p => p.1 == [a, b, c, d] && wf4 p.2 && invCode p.2 &&
      mulCols 4 p.2 T0cols == mulCols 4 [a, b, c, d] p.2

@[expose] def TFactsA (a : ℕ) : Bool :=
  (List.range 16).all fun b => (List.range 16).all fun c => (List.range 16).all fun d =>
    tLeafK a b c d

end CFSG.KC.TransvK
