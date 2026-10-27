module

public import Certificates.Data.GrSLitL34FactsCF23SuzCheck
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.SuzOddCore.Arrays

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GSThmB.CF23L34

@[expose] def suzCtrlGens : Array (Array Nat) :=
  #[suzY1Arr, suzY2Arr, compA 1782 (compA 1782 suzMArr suzY1Arr) (invCand 1782 suzMArr),
    compA 1782 (compA 1782 suzMArr suzY2Arr) (invCand 1782 suzMArr)]

@[expose] def suzCtrlGensInv : Array (Array Nat) := suzCtrlGens.map (invCand 1782)

@[expose] def suzCtrlWordB0 : List Int :=
  [-4, -1, 4, 2, -1, -3, 4, 4, 1, 4, 4, 1, 2, 1, -2, 3, 1, -4, -4, -2]

@[expose] def suzCtrlWordB1 : List Int :=
  [-1, 4, -3, -1, -4, -4, -1, 2, 4, 3, 1, 4, 3, -4, 1, 3, 1, -4, -2, 1, 2, 3, 1, 3, -4, -4, 3, 4,
    1, -4, -2, 1, -4, -2, 1, 2, 4, 1, 2, 4, 1, 2, 4, 2, 4, 4, 2]

@[noinline, expose] def suzCtrlGenOK : Bool :=
  isInvA 1782 suzCtrlGens[0]! suzCtrlGensInv[0]! && isInvA 1782 suzCtrlGens[1]! suzCtrlGensInv[1]! &&
    isInvA 1782 suzCtrlGens[2]! suzCtrlGensInv[2]! &&
    isInvA 1782 suzCtrlGens[3]! suzCtrlGensInv[3]! &&
    lettersOK 4 suzCtrlWordB0 && lettersOK 4 suzCtrlWordB1 &&
    eqA 1782 (wordA 1782 suzCtrlGens suzCtrlGensInv suzCtrlWordB0) b0Arr &&
    eqA 1782 (wordA 1782 suzCtrlGens suzCtrlGensInv suzCtrlWordB1) b1Arr

end CFSG.ComponentClassification.GrSLit.L34Sec5S
