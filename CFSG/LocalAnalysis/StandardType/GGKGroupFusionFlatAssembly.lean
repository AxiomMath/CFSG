module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionFlatFamilies
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionFlatSeitzExc
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExc
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionRestOuter
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionRestAlt
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKHolds
public import CFSG.LocalAnalysis.StandardType.GGSeitzExcInputsHolds
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionFlatRestEight

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Assembly

theorem ggKGroupFusionAtFlat_seitzException_of_inputs
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog) (h : GGSeitzExcInputs) :
    GGKGroupFusionAtFlat GGKFLieSeitzException := by
  obtain ⟨hU, hT3, hT5, hO8, hC8, hO6, hC6, hO4, hC4⟩ := h
  exact ggKGroupFusionAtFlat_seitzException_of (ggKGroupFusionAtFlat_lTwoEight hSch)
    (ggKGroupFusionAtFlat_lThreeFour hSch hO4 hC4) (ggKGroupFusionAtFlat_uFourTwo hSch hU)
    (ggKGroupFusionAtFlat_spSixTwo hSch hO6 hC6) (ggKGroupFusionAtFlat_spEightTwo hSch hO8 hC8)
    (ggKGroupFusionAtFlat_titsThree hSch hT3) (ggKGroupFusionAtFlat_titsFive hSch hT5)
    (ggKGroupFusionAtFlat_szThirtyTwo hSch)

end Assembly

section Rest

open CFSG.LocalAnalysis.ComponentInitial CFSG.AGLEmbeddingD2 in
theorem ggKGroupFusionLayerInputFlat_of_rest8FlatK (hSch : SchreierFor InCatalog)
    (hS : KFactSeitzRankTwo) (h : GGKGroupFusionRest8FlatK) : GGKGroupFusionLayerInputFlat :=
  ggKGroupFusionLayerInputFlat_of_atK hSch
    (ggKGroupFusionAtFlatK_of_families (ggKGroupFusionAtFlat_alternating_of ggAltNotMarkedInput)
      (ggKGroupFusionAtFlat_lieDefining_of_inputs hSch h.1
        (ggLieOuterFieldAutInput_of ggLieOutRankTwoInput_holds h.2.1))
      (ggKGroupFusionAtFlat_lieCross_of_seitz hS
        (ggKGroupFusionAtFlat_seitzException_of_inputs hSch ggSeitzExcInputs_holds))
      h.2.2)

end Rest

end CFSG.StandardType
