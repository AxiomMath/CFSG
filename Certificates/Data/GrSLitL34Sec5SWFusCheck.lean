module

public import Certificates.Data.GrSLitL34Sec5SWIsoCheck

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def commKB (kb : List Bool) (x y : MElt) : Bool := eqKB kb (mulM x y) (mulM y x)

@[noinline, expose] def twoEightsOK (kb : List Bool) : Bool :=
  let I := dedupKB kb (allM.filter (isInvKB kb))
  I.any fun x₁ => I.any fun x₂ => !eqKB kb x₂ x₁ && commKB kb x₁ x₂ &&
    let C := I.filter fun y => commKB kb y x₁ && commKB kb y x₂
    C.any fun x₃ => C.any fun x₄ => !commKB kb x₃ x₄

@[expose] def zInvs : List MElt := [(0, 2, 0), (0, 0, 2), (0, 2, 2)]

@[noinline, expose] def fieldSqOK : Bool :=
  let kb := kbOfMask 1
  outerInvs.all fun p => !liftsKB kb p.2 || typeOf p.1 p.2 != 0 ||
    zInvs.all fun z => !fixKB kb p.1 p.2 z ||
      allM.any fun x => fixKB kb p.1 p.2 x && eqKB kb (mulM x x) z

end CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
