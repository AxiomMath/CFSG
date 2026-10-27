module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalSL
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem ggSixBstarNoOffenderAt_PSL_of_rest (hDvd : GGSixBstarNoOffenderOn GGPSLSplitDvd)
    (hNs : GGSixBstarNoOffenderOn GGPSLNonsplit) : GGSixBstarNoOffenderAt .PSL :=
  ggSixBstarNoOffenderAt_PSL_of_on
    (ggSixBstarNoOffenderOn_PSLSplit_of_on ggSixBstarNoOffenderOn_PSLSplitCoprime hDvd) hNs

@[expose] def GGSixBstarNoOffenderRest6 : Prop :=
  GGSixBstarNoOffenderOn GGPSLSplitDvd ∧ GGSixBstarNoOffenderOn GGPSLNonsplit ∧
    GGSixBstarNoOffenderOn GGPSpNonsplit ∧ GGSixBstarNoOffenderAt .PSU ∧
      GGSixBstarNoOffenderAt .POmegaPlus ∧ GGSixBstarNoOffenderAt .POmegaMinus ∧
        GGSixBstarNoOffenderAt .F4 ∧ GGSixBstarNoOffenderAt .E6 ∧ GGSixBstarNoOffenderAt .E7 ∧
          GGSixBstarNoOffenderAt .E8 ∧ GGSixBstarNoOffenderAt .twistedE6

theorem ggSixBstarNoOffenderRest5_of_rest6 (h : GGSixBstarNoOffenderRest6) :
    GGSixBstarNoOffenderRest5 := by
  obtain ⟨hDvd, hLNs, hpNs, hPSU, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ⟨ggSixBstarNoOffenderAt_PSL_of_rest hDvd hLNs, hPSU,
    ggSixBstarNoOffenderAt_PSp_of_nonsplit hpNs, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩

theorem ggSixBstarNoOffenderInput_of_rest6 (h : GGSixBstarNoOffenderRest6) :
    GGSixBstarNoOffenderInput :=
  ggSixBstarNoOffenderInput_of_rest5 (ggSixBstarNoOffenderRest5_of_rest6 h)

theorem ggSixBstarUniqueV2Input_of_rest6 (h : GGSixBstarNoOffenderRest6) :
    GGSixBstarUniqueV2Input :=
  ggSixBstarUniqueV2Input_of_noOffender (ggSixBstarNoOffenderInput_of_rest6 h)

end Inputs

end CFSG.StandardType
