module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3Conj
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3Layer

public section

namespace CFSG.StandardType

section Assembly

theorem ggSixTrialityInput_of_lSixEleven_dClassThree (h611 : GGSixLSixElevenInput)
    (h6 : GGSixTrialityDClassThreeInput) : GGSixTrialityInput :=
  ggSixTrialityInput_of_std h611 ggD4ClassThreeConjInput_holds ggD4ClassThreeStdSylowInput_holds
    ggD4ClassThreeLayerStdInput_holds h6

end Assembly

end CFSG.StandardType
