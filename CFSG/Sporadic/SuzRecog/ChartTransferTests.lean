module

public import CFSG.Sporadic.SuzRecog.TwistTests
public meta import CFSG.Sporadic.SuzRecog.TwistTests

public section

namespace CFSG.Sporadic.SuzRecog.RigidL2

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore

@[expose] def chartWord : List Nat :=
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0]

@[expose] def bLetterTab (k : Nat) : Array Nat := if k == 0 then b0Arr else b1Arr

@[expose] def bWordTab (w : List Nat) : Array Nat :=
  w.foldr (fun k t => compA 1782 (bLetterTab k) t) (idA 1782)

@[expose] def chartTab : Array Nat := bWordTab chartWord

@[expose] def chartSwapOK : Bool :=
  chartWord.all (fun k => decide (k < 2)) &&
    eqA 1782 (compA 1782 chartTab tTab) (compA 1782 w0Tab chartTab) &&
    eqA 1782 (compA 1782 tTab chartTab) (compA 1782 chartTab w0Tab)

end CFSG.Sporadic.SuzRecog.RigidL2
