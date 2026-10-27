module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresSp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresSU
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAlt
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresHerm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem ggSpCentralizerCoreInput_holds : GGSpCentralizerCoreInput :=
  LayerCores.ggSpCentralizerCoreInput_of LayerCores.hermCoreInput_holds
    LayerCores.altCoreInput_holds

theorem ggSUCentralizerCoreInput_holds : GGSUCentralizerCoreInput :=
  LayerCores.ggSUCentralizerCoreInput_of LayerCores.hermCoreInput_holds
    LayerCores.altCoreInput_holds

section Tags

theorem ggLayerTags_PSp : GGLayerCentreOddTag .PSp ∧ GGLayerPerfectTag .PSp :=
  ggLayerTags_PSp_of_core ggSpCentralizerCoreInput_holds

theorem ggLayerTags_PSU : GGLayerCentreOddTag .PSU ∧ GGLayerPerfectTag .PSU :=
  ggLayerTags_PSU_of_core ggSUCentralizerCoreInput_holds

theorem ggLayerInputs_of_remaining_seven
    (hPlus : GGLayerCentreOddTag .POmegaPlus ∧ GGLayerPerfectTag .POmegaPlus)
    (hMinus : GGLayerCentreOddTag .POmegaMinus ∧ GGLayerPerfectTag .POmegaMinus)
    (hF4 : GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4)
    (hE6 : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6)
    (hE7 : GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7)
    (hE8 : GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8)
    (hTwE6 : GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_remaining_cores ggSUCentralizerCoreInput_holds ggSpCentralizerCoreInput_holds
    hPlus hMinus hF4 hE6 hE7 hE8 hTwE6

end Tags

end CFSG.StandardType
