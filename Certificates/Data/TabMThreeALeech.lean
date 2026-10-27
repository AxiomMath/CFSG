module

public import Certificates.Data.CFSGNative.Co1.Odd
public import CFSG.Sporadic.Co1.Module.OddProg
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import CFSG.Sporadic.Co1.Module.OddProg
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public meta import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.Setup
public meta import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Suz.W64Spec

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.Module.Odd
  CFSG.Sporadic.Co1.OddNative CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native

@[expose] def c0Rows (_ : Unit := ()) : Rows := mul (rr 27) (rr 70)

@[expose] def threeARows (_ : Unit := ()) : Rows := mul (mul (aRows 1) (aRows 4)) (aRows 5)

@[expose] def threeAFix (_ : Unit := ()) : List Nat :=
  [fixCount [transposeRows 24 (c0Rows ())], fixCount [transposeRows 24 (rootRows 0)],
    fixCount [transposeRows 24 (rootRows 2)], fixCount [transposeRows 24 (threeARows ())]]

end CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech
