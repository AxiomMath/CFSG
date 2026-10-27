module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTailSchur
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTailCanon
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTailDFour

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Assembly

theorem ggStepTwoAutKRestInput_of_tail (h3 : GGAutKCanonIIIInput) (h4 : GGAutKCanonIVInput)
    (hF : GGSixFieldFiveInput) (hD : GGLayerNotDFourTwoInput) (hC : GGStepTwoChoiceThreeInput) :
    GGStepTwoAutKRestInput :=
  ggStepTwoAutKRestInput_of_finest' ggAutKCanonIIInput_holds h3 h4 ggAltFiveCentreInput_holds hF
    hD hC

theorem ggStepTwoAutKFiveInput_of_tailTags (hF : GGSixFieldFiveInput)
    (hPSU : GGLayerNotDFourTwoTag .PSU) (hPSp : GGLayerNotDFourTwoTag .PSp)
    (hPlus : GGLayerNotDFourTwoTag .POmegaPlus) (hMinus : GGLayerNotDFourTwoTag .POmegaMinus)
    (hF4 : GGLayerNotDFourTwoTag .F4) (hE6 : GGLayerNotDFourTwoTag .E6)
    (hE7 : GGLayerNotDFourTwoTag .E7) (hE8 : GGLayerNotDFourTwoTag .E8)
    (hTwE6 : GGLayerNotDFourTwoTag .twistedE6) : GGStepTwoAutKFiveInput :=
  ggStepTwoAutKFiveInput_of_field hF
    (ggLayerNotDFourTwoInput_of_remaining hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6)

theorem ggStepTwoAutKRestInput_of_tailTags (h3 : GGAutKCanonIIIInput) (h4 : GGAutKCanonIVInput)
    (hF : GGSixFieldFiveInput) (hPSU : GGLayerNotDFourTwoTag .PSU)
    (hPSp : GGLayerNotDFourTwoTag .PSp) (hPlus : GGLayerNotDFourTwoTag .POmegaPlus)
    (hMinus : GGLayerNotDFourTwoTag .POmegaMinus) (hF4 : GGLayerNotDFourTwoTag .F4)
    (hE6 : GGLayerNotDFourTwoTag .E6) (hE7 : GGLayerNotDFourTwoTag .E7)
    (hE8 : GGLayerNotDFourTwoTag .E8) (hTwE6 : GGLayerNotDFourTwoTag .twistedE6)
    (hC : GGStepTwoChoiceThreeInput) : GGStepTwoAutKRestInput :=
  ggStepTwoAutKRestInput_of_tail h3 h4 hF
    (ggLayerNotDFourTwoInput_of_remaining hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6) hC

end Assembly

end CFSG.StandardType
