module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltFamily
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltDefining

public section

namespace CFSG.StandardType

open CFSG.Assembly

open CFSG.LocalAnalysis.ComponentInitial CFSG.AGLEmbeddingD2 in
theorem ggKGroupFusionLayerInput_of_reduced (hSch : SchreierFor InCatalog)
    (hS : KFactSeitzRankTwo) (hNM : GGAltNotMarkedInput) (hpar : GGLieParabolicCharInput)
    (hout : GGLieOuterFieldAutInput) (hX : GGKGroupFusionAt GGKFLieSeitzException)
    (hSp : GGKGroupFusionAt GGKFSporadic) : GGKGroupFusionLayerInput :=
  ggKGroupFusionLayerInput_of_families hSch hS (ggKGroupFusionAt_alternating_of hNM)
    (ggKGroupFusionAt_lieDefining_of_inputs hSch hpar hout) hX hSp

section Inputs

open CFSG.LocalAnalysis.ComponentInitial CFSG.AGLEmbeddingD2 in
theorem ggSixStepTwoV2Input_of_reduced (hSch : SchreierFor InCatalog) (hS : KFactSeitzRankTwo)
    (hNM : GGAltNotMarkedInput) (hpar : GGLieParabolicCharInput) (hout : GGLieOuterFieldAutInput)
    (hKX : GGKGroupFusionAt GGKFLieSeitzException) (hKS : GGKGroupFusionAt GGKFSporadic)
    (h613 : GGStepTwoLemmaSixThirteenInput) (hA : GGStepTwoLinearFusionInput)
    (hR : GGStepTwoAutKRestInput) (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_kgroupFamilies hSch hS (ggKGroupFusionAt_alternating_of hNM)
    (ggKGroupFusionAt_lieDefining_of_inputs hSch hpar hout) hKX hKS h613 hA hR h615

end Inputs

end CFSG.StandardType
