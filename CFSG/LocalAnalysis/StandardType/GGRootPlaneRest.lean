module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneRestSU
public import CFSG.LocalAnalysis.StandardType.GGRootPlaneRestSp
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRest
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestSL

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGRootPlaneRest6 : Prop :=
  GGRootPlaneInputOn GGPSpNonsplit ∧ GGRootPlaneAt .POmegaPlus ∧ GGRootPlaneAt .POmegaMinus ∧
    GGRootPlaneAt .F4 ∧ GGRootPlaneAt .E6 ∧ GGRootPlaneAt .E7 ∧ GGRootPlaneAt .E8 ∧
      GGRootPlaneAt .twistedE6

theorem ggRootPlaneRest5_of_rest6 (h : GGRootPlaneRest6) : GGRootPlaneRest5 := by
  obtain ⟨hSp, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ⟨ggRootPlaneInputOn_PSUNonsplit, hSp, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩

theorem ggRootPlaneInput_of_rest6 (h : GGRootPlaneRest6) : GGRootPlaneInput :=
  ggRootPlaneInput_of_rest5 ggSLNonsplitFrameInput_holds (ggRootPlaneRest5_of_rest6 h)

theorem ggRootPlaneInputOn_notPSLSplit_of_rest6 (h : GGRootPlaneRest6) :
    GGRootPlaneInputOn fun t n f p => ¬ GGPSLSplit t n f p :=
  ggRootPlaneInputOn_notPSLSplit_of_rest5 ggSLNonsplitFrameInput_holds (ggRootPlaneRest5_of_rest6 h)

@[expose] def GGRootPlaneRestOmegaExc : Prop :=
  GGRootPlaneAt .POmegaPlus ∧ GGRootPlaneAt .POmegaMinus ∧ GGRootPlaneAt .F4 ∧
    GGRootPlaneAt .E6 ∧ GGRootPlaneAt .E7 ∧ GGRootPlaneAt .E8 ∧ GGRootPlaneAt .twistedE6

theorem ggRootPlaneRest6_of_sp (hSp : GGRootPlaneInputOn GGPSpNonsplit)
    (h : GGRootPlaneRestOmegaExc) : GGRootPlaneRest6 := by
  obtain ⟨hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ⟨hSp, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩

theorem ggRootPlaneRest6_of_frame_comp (hF : GGSpNonsplitFrameInput)
    (hC : GGSpNonsplitCompInput) (h : GGRootPlaneRestOmegaExc) : GGRootPlaneRest6 :=
  ggRootPlaneRest6_of_sp (ggRootPlaneInputOn_PSpNonsplit_of_frame_comp hF hC) h

theorem ggRootPlaneInput_of_frame_comp (hF : GGSpNonsplitFrameInput)
    (hC : GGSpNonsplitCompInput) (h : GGRootPlaneRestOmegaExc) : GGRootPlaneInput :=
  ggRootPlaneInput_of_rest6 (ggRootPlaneRest6_of_frame_comp hF hC h)

end Inputs

end CFSG.StandardType
