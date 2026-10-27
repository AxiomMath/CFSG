module

public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216Inputs

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I.L216

open CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.GH74.KGroups

@[expose] def l216CosetOK : Bool :=
  !(QP.sift (sg * sg) 0) && (elemsT QA).all fun g => !decide (g * g = 1) || decide (g = 1) ||
    (elemsT QP).any fun c => decide (c * g * c⁻¹ = pa) || decide (c * g * c⁻¹ = sg * sg)

end CFSG.ComponentClassification.GSThmB.CF23I.L216
