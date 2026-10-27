module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFree
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem ggOrthCentralizerCoreInput_holds : GGOrthCentralizerCoreInput :=
  ggOrthCentralizerCoreInput_of ggOrthRegularCoreInput_holds ggOrthFreeCoreInput_holds

section Tags

theorem ggLayerTags_POmegaPlus : GGLayerCentreOddTag .POmegaPlus ∧ GGLayerPerfectTag .POmegaPlus :=
  ggLayerTags_POmegaPlus_of_core ggOrthCentralizerCoreInput_holds

theorem ggLayerTags_POmegaMinus :
    GGLayerCentreOddTag .POmegaMinus ∧ GGLayerPerfectTag .POmegaMinus :=
  ggLayerTags_POmegaMinus_of_core ggOrthCentralizerCoreInput_holds

theorem ggLayerInputs_of_remaining_five
    (hF4 : GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4)
    (hE6 : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6)
    (hE7 : GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7)
    (hE8 : GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8)
    (hTwE6 : GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_remaining_seven ggLayerTags_POmegaPlus ggLayerTags_POmegaMinus hF4 hE6 hE7 hE8
    hTwE6

end Tags

end CFSG.StandardType
