module

public import CFSG.LocalAnalysis.StandardType.GGO2CentralizerG0Holds
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvPSp
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvAtF4
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvAtE78

public section

namespace CFSG.StandardType

theorem ggOuterInvAt_PSp
    : GGOuterInvAt .PSp :=
  ggOuterInvAt_of_fieldTags (Or.inl rfl) (ggO2CentralizerG0At_holds .PSp)
    ggFieldOuterInvAt_PSp

theorem ggOuterInvAt_F4
    : GGOuterInvAt .F4 :=
  ggOuterInvAt_of_fieldTags (Or.inr (Or.inl rfl)) (ggO2CentralizerG0At_holds .F4)
    ggFieldOuterInvAt_F4

theorem ggOuterInvAt_E7
    : GGOuterInvAt .E7 :=
  ggOuterInvAt_of_fieldTags (Or.inr (Or.inr (Or.inl rfl))) (ggO2CentralizerG0At_holds .E7)
    (ggFieldOuterInvAt_E78 .E7 (Or.inl rfl))

theorem ggOuterInvAt_E8
    : GGOuterInvAt .E8 :=
  ggOuterInvAt_of_fieldTags (Or.inr (Or.inr (Or.inr rfl))) (ggO2CentralizerG0At_holds .E8)
    (ggFieldOuterInvAt_E78 .E8 (Or.inr rfl))

end CFSG.StandardType
