module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
public meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests

public section

namespace CFSG.ComponentClassification.AS81.SuzB0

open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore

@[expose] def tauWord : List Int :=
  [-3, -2, -1, -2, -3, -1, 2, -3, -1, 3, -2, 3, -2, 1, 3, 1, 3, 1, -2, -3, -2, 1, 2, 2, -1, -3,
    -1, 2, -3, 2, 1, 2, -1, 2, -1, -2, -3, -1, -2, -3, -2, -3, -2, -1, -3, -2, -1, -3, -2, -1,
    -3, -2, 1, -2, 1, 2, 3, -2, 1, 3, 1, -2, 1, -2, 1, -2, 1, 2, 3, -2, 1, 3, 1, -2, -1, -3]

@[expose] def tauActs : List (Nat × Nat) := [(1, 1), (27, 1), (44, 0), (5, 1), (33, 1), (52, 0)]

@[expose] def tauAct (i : Nat) : Nat × Nat := tauActs.getD i (0, 0)

@[expose] def tauArr (_ : Unit := ()) : Array Nat := wordA 1782 bTriple bTripleInv tauWord

@[expose] def tauMatTab (_ : Unit := ()) : Array Nat :=
  Array.ofFn (n := 64) fun v =>
    (List.range 6).foldl (fun r i => if v.val.testBit i then r ^^^ (tauAct i).1 else r) 0

@[expose] def tauCheck (_ : Unit := ()) : Bool :=
  let τ := tauArr ()
  lettersOK 3 tauWord && permOK 1782 τ && commutesA τ tTab &&
    (allBelow 6 fun i =>
      eqA 1782 (compA 1782 (compA 1782 τ (qArr i)) (invCand 1782 τ))
        (compA 1782 qProds[(tauAct i).1]! (tPow (tauAct i).2))) &&
    notInOK matEnum.tabs (tauMatTab ())

end CFSG.ComponentClassification.AS81.SuzB0
