module

public import CFSG.Sporadic.SuzRecog.LevelTwoCheck

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwo.WCheck

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0

@[expose] def c3Arr : Array Nat := (invInnerGenArrs 1)[3]!

@[expose] def c6Arr : Array Nat := (invInnerGenArrs 1)[6]!

@[expose] def wConjArr : Array Nat :=
  compA 1782 c3Arr (compA 1782 c6Arr (compA 1782 (qProd 1)
    (compA 1782 (invCand 1782 c6Arr) (invCand 1782 c3Arr))))

@[expose] def wOK : Bool := eqA 1782 (compA 1782 t1Arr aPts[p1]!) wConjArr

end CFSG.Sporadic.SuzRecog.LevelTwo.WCheck
