module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcLTwoEight
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcSolv
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcSz
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcGenuine
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.AGLEmbeddingD2

@[expose] def GGSeitzExcInputs : Prop :=
  GGSeitzExcUFourTwoInput ∧ GGSeitzExcTitsThreeInput ∧
    GGSeitzExcTitsFiveInput ∧ GGSeitzExcSpEightOvergroupInput ∧
    GGSeitzExcSpEightCentralizerInput ∧ GGSeitzExcSpSixOvergroupInput ∧
    GGSeitzExcSpSixCentralizerInput ∧ GGSeitzExcLThreeFourOvergroupInput ∧
    GGSeitzExcLThreeFourCentralizerInput

section Assembly


theorem ggKGroupFusionAt_seitzException_of_inputs
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog) (h : GGSeitzExcInputs) :
    GGKGroupFusionAt GGKFLieSeitzException := by
  obtain ⟨hU, hT3, hT5, hO8, hC8, hO6, hC6, hO4, hC4⟩ := h
  exact ggKGroupFusionAt_seitzException_of (ggKGroupFusionAt_lTwoEight hSch)
    (ggKGroupFusionAt_lThreeFour hSch hO4 hC4) (ggKGroupFusionAt_uFourTwo hSch hU)
    (ggKGroupFusionAt_spSixTwo hSch hO6 hC6) (ggKGroupFusionAt_spEightTwo hSch hO8 hC8)
    (ggKGroupFusionAt_titsThree hSch hT3) (ggKGroupFusionAt_titsFive hSch hT5)
    (ggKGroupFusionAt_szThirtyTwo hSch)

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggKGroupFusionLayerInput_of_seitzExcInputs (hSch : SchreierFor InCatalog)
    (hS : KFactSeitzRankTwo) (hNM : GGAltNotMarkedInput) (hpar : GGLieParabolicCharInput)
    (hout : GGLieOuterFieldAutInput) (hX : GGSeitzExcInputs)
    (hSp : GGKGroupFusionAt GGKFSporadic) : GGKGroupFusionLayerInput :=
  ggKGroupFusionLayerInput_of_reduced hSch hS hNM hpar hout
    (ggKGroupFusionAt_seitzException_of_inputs hSch hX) hSp

end Assembly

end CFSG.StandardType
