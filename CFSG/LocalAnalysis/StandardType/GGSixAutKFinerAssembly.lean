module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerOrbit
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerThree
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Assembly

theorem ggStepTwoAutKRestInput_of_finest (h2 : GGAutKCanonIIInput) (h3 : GGAutKCanonIIIInput)
    (h4 : GGAutKCanonIVInput) (hN : GGStepTwoBstarNormFiveInput) (hF : GGSixFieldFiveInput)
    (hD : GGLayerNotDFourTwoInput) (hC : GGStepTwoChoiceThreeInput) : GGStepTwoAutKRestInput :=
  ggStepTwoAutKRestInput_of_finer (ggSixAutKHypRestAtInput_of_canon h2 h3 h4)
    (ggStepTwoAutKFiveInput_of_finer hN hF hD) (ggStepTwoAutKThreeInput_of_choice hC)

theorem ggStepTwoAutKRestInput_of_finest' (h2 : GGAutKCanonIIInput) (h3 : GGAutKCanonIIIInput)
    (h4 : GGAutKCanonIVInput) (hS : GGAltFiveCentreInput) (hF : GGSixFieldFiveInput)
    (hD : GGLayerNotDFourTwoInput) (hC : GGStepTwoChoiceThreeInput) : GGStepTwoAutKRestInput :=
  ggStepTwoAutKRestInput_of_finest h2 h3 h4 (ggStepTwoBstarNormFiveInput_of_schur hS) hF hD hC

end Assembly

end CFSG.StandardType
