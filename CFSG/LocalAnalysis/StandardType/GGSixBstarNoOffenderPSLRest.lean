module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRestSplit
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRestNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRestSp
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUOSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem ggSixBstarNoOffenderAt_PSL_holds : GGSixBstarNoOffenderAt .PSL :=
  ggSixBstarNoOffenderAt_PSL_of_on ggSixBstarNoOffenderOn_PSLSplitProj
    ggSixBstarNoOffenderOn_PSLNonsplit

@[expose] def GGSixBstarNoOffenderRestPSL : Prop :=
  GGSixBstarNoOffenderOn GGPSpNonsplit ∧ GGSixBstarNoOffenderOn GGPSUNonsplit ∧
    GGSixBstarNoOffenderAt .POmegaPlus ∧ GGSixBstarNoOffenderAt .POmegaMinus ∧
      GGSixBstarNoOffenderAt .F4 ∧ GGSixBstarNoOffenderAt .E6 ∧ GGSixBstarNoOffenderAt .E7 ∧
        GGSixBstarNoOffenderAt .E8 ∧ GGSixBstarNoOffenderAt .twistedE6

theorem ggSixBstarNoOffenderRestUO_of_restPSL (h : GGSixBstarNoOffenderRestPSL) :
    GGSixBstarNoOffenderRestUO := by
  obtain ⟨hpNs, hUNs, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ⟨ggSixBstarNoOffenderOn_PSLSplitDvd, ggSixBstarNoOffenderOn_PSLNonsplit, hpNs, hUNs, hPlus,
    hMinus, hF4, hE6, hE7, hE8, hTwE6⟩

theorem ggSixBstarNoOffenderRest6_of_restPSL (h : GGSixBstarNoOffenderRestPSL) :
    GGSixBstarNoOffenderRest6 :=
  ggSixBstarNoOffenderRest6_of_restUO (ggSixBstarNoOffenderRestUO_of_restPSL h)

theorem ggSixBstarNoOffenderInput_of_restPSL (h : GGSixBstarNoOffenderRestPSL) :
    GGSixBstarNoOffenderInput :=
  ggSixBstarNoOffenderInput_of_restUO (ggSixBstarNoOffenderRestUO_of_restPSL h)

theorem ggSixBstarUniqueV2Input_of_restPSL (h : GGSixBstarNoOffenderRestPSL) :
    GGSixBstarUniqueV2Input :=
  ggSixBstarUniqueV2Input_of_restUO (ggSixBstarNoOffenderRestUO_of_restPSL h)

end Inputs

end CFSG.StandardType
