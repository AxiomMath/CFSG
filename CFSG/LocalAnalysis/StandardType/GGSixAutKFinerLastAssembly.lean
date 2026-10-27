module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerLastChoice
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTailAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Assembly

theorem ggStepTwoAutKRestInput_of_last (h3 : GGAutKCanonIIIInput) (h4 : GGAutKCanonIVInput)
    (hF : GGSixFieldFiveInput)
    (hD : GGLayerNotDFourTwoTag .PSU ∧ GGLayerNotDFourTwoTag .PSp ∧
      GGLayerNotDFourTwoTag .POmegaPlus ∧ GGLayerNotDFourTwoTag .POmegaMinus ∧
        GGLayerNotDFourTwoTag .F4 ∧ GGLayerNotDFourTwoTag .E6 ∧ GGLayerNotDFourTwoTag .E7 ∧
          GGLayerNotDFourTwoTag .E8 ∧ GGLayerNotDFourTwoTag .twistedE6)
    (hUA : GGLayerNotUFourAltSixRest) (h2 : GGStepTwoChoiceThreeTwoRest) :
    GGStepTwoAutKRestInput :=
  ggStepTwoAutKRestInput_of_tailTags h3 h4 hF hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1
    hD.2.2.2.2.2.1 hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.2
    (ggStepTwoChoiceThreeInput_of_remaining hD hUA h2)

end Assembly

end CFSG.StandardType
