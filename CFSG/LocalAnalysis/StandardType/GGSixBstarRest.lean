module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestPlane
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSU
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSpFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGRootPlaneRest5 : Prop :=
  GGRootPlaneInputOn GGPSUNonsplit ∧ GGRootPlaneInputOn GGPSpNonsplit ∧
    GGRootPlaneAt .POmegaPlus ∧ GGRootPlaneAt .POmegaMinus ∧ GGRootPlaneAt .F4 ∧
      GGRootPlaneAt .E6 ∧ GGRootPlaneAt .E7 ∧ GGRootPlaneAt .E8 ∧ GGRootPlaneAt .twistedE6

theorem ggRootPlaneInputOn_notPSLSplit_of_rest5 (hF : GGSLNonsplitFrameInput)
    (h : GGRootPlaneRest5) : GGRootPlaneInputOn fun t n f p => ¬ GGPSLSplit t n f p := by
  obtain ⟨hSU, hSp, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ggRootPlaneInputOn_notPSLSplit_of_frame_rest hF (ggRootPlaneAt_PSU_of_nonsplit hSU)
    (ggRootPlaneAt_PSp_of_nonsplit hSp) hPlus hMinus hF4 hE6 hE7 hE8 hTwE6

theorem ggRootPlaneInput_of_rest5 (hF : GGSLNonsplitFrameInput) (h : GGRootPlaneRest5) :
    GGRootPlaneInput :=
  ggRootPlaneInput_of_notPSLSplit (ggRootPlaneInputOn_notPSLSplit_of_rest5 hF h)

@[expose] def GGSixBstarNoOffenderRest5 : Prop :=
  GGSixBstarNoOffenderAt .PSL ∧ GGSixBstarNoOffenderAt .PSU ∧ GGSixBstarNoOffenderAt .PSp ∧
    GGSixBstarNoOffenderAt .POmegaPlus ∧ GGSixBstarNoOffenderAt .POmegaMinus ∧
      GGSixBstarNoOffenderAt .F4 ∧ GGSixBstarNoOffenderAt .E6 ∧ GGSixBstarNoOffenderAt .E7 ∧
        GGSixBstarNoOffenderAt .E8 ∧ GGSixBstarNoOffenderAt .twistedE6

theorem ggSixBstarNoOffenderInput_of_rest5 (h : GGSixBstarNoOffenderRest5) :
    GGSixBstarNoOffenderInput := by
  obtain ⟨hPSL, hPSU, hPSp, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ggSixBstarNoOffenderInput_of_remaining hPSL hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6

theorem ggSixBstarUniqueV2Input_of_rest5 (h : GGSixBstarNoOffenderRest5) :
    GGSixBstarUniqueV2Input :=
  ggSixBstarUniqueV2Input_of_noOffender (ggSixBstarNoOffenderInput_of_rest5 h)

end Inputs

end CFSG.StandardType
