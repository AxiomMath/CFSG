module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaSU
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaD4
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaPM
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem ggSixBstarNoOffenderAt_POmegaPlus_of_d4OrthFrame
    (hD4 : GGSixBstarOrthFrameOn GGPOmegaPlusD4Three) : GGSixBstarNoOffenderAt .POmegaPlus :=
  ggSixBstarNoOffenderAt_POmegaPlus_of_D4 (ggNoOffender_of_orthFrameOn hD4)

@[expose] def GGSixBstarNoOffenderRestOm : Prop :=
  GGSixBstarNoOffenderOn GGPSpNonsplit ∧ GGSixBstarOrthFrameOn GGPOmegaPlusD4Three ∧
    GGSixBstarNoOffenderAt .F4 ∧ GGSixBstarNoOffenderAt .E6 ∧ GGSixBstarNoOffenderAt .E7 ∧
      GGSixBstarNoOffenderAt .E8 ∧ GGSixBstarNoOffenderAt .twistedE6

theorem ggSixBstarNoOffenderRestPSL_of_restOm (h : GGSixBstarNoOffenderRestOm) :
    GGSixBstarNoOffenderRestPSL := by
  obtain ⟨hpNs, hD4, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ⟨hpNs, ggSixBstarNoOffenderOn_PSUNonsplit,
    ggSixBstarNoOffenderAt_POmegaPlus_of_d4OrthFrame hD4, ggSixBstarNoOffenderAt_POmegaMinus, hF4,
    hE6, hE7, hE8, hTwE6⟩

theorem ggSixBstarNoOffenderRestUO_of_restOm (h : GGSixBstarNoOffenderRestOm) :
    GGSixBstarNoOffenderRestUO :=
  ggSixBstarNoOffenderRestUO_of_restPSL (ggSixBstarNoOffenderRestPSL_of_restOm h)

theorem ggSixBstarNoOffenderInput_of_restOm (h : GGSixBstarNoOffenderRestOm) :
    GGSixBstarNoOffenderInput :=
  ggSixBstarNoOffenderInput_of_restPSL (ggSixBstarNoOffenderRestPSL_of_restOm h)

theorem ggSixBstarUniqueV2Input_of_restOm (h : GGSixBstarNoOffenderRestOm) :
    GGSixBstarUniqueV2Input :=
  ggSixBstarUniqueV2Input_of_restPSL (ggSixBstarNoOffenderRestPSL_of_restOm h)

end Inputs

end CFSG.StandardType
