module

public import CFSG.LocalAnalysis.StandardType.GGAssemblySevenDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeSL
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeSp
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmega
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmRest
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiag
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarOrthFrameD4
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClHerm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClAltSix
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLTag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGStepTwoToralRound8 : Prop :=
  GGSpCoordModelNonsplitInput ∧ GGStepTwoCoordModelOn .PSU ∧ GGStepTwoCoordModelOn .POmegaPlus ∧
    GGStepTwoCoordModelOn .POmegaMinus ∧ GGStepTwoToralWitnessRestInput

theorem ggStepTwoToralRound5_of_round8 (h : GGStepTwoToralRound8) : GGStepTwoToralRound5 :=
  ⟨ggStepTwoCoordModelOn_PSL_holds, h.2.1, ggStepTwoCoordModelOn_PSp_of_nonsplit h.1, h.2.2.1,
    h.2.2.2.1, h.2.2.2.2⟩

theorem ggSixBstarNoOffenderRestOm_of_round8 (h : GGSixBstarNoOffenderAt .F4 ∧
    GGSixBstarNoOffenderAt .E6 ∧ GGSixBstarNoOffenderAt .E7 ∧ GGSixBstarNoOffenderAt .E8 ∧
    GGSixBstarNoOffenderAt .twistedE6) :
    GGSixBstarNoOffenderRestOm :=
  ggSixBstarNoOffenderRestOm_of_rest ggSixBstarNoOffenderOn_PSpNonsplit h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2

@[expose] def GGNonsplitCompLiftRound8 : Prop :=
  GGNonsplitCompLiftTag .POmegaPlus ∧ GGNonsplitCompLiftTag .POmegaMinus ∧
    GGNonsplitCompLiftTag .F4 ∧ GGNonsplitCompLiftTag .E6 ∧ GGNonsplitCompLiftTag .E7 ∧
      GGNonsplitCompLiftTag .E8 ∧ GGNonsplitCompLiftTag .twistedE6

@[expose] def GGNonsplitNbrMarkingRound8 : Prop :=
  GGNonsplitNbrMarkingTag .POmegaPlus ∧ GGNonsplitNbrMarkingTag .POmegaMinus ∧
    GGNonsplitNbrMarkingTag .F4 ∧ GGNonsplitNbrMarkingTag .E6 ∧ GGNonsplitNbrMarkingTag .E7 ∧
      GGNonsplitNbrMarkingTag .E8 ∧ GGNonsplitNbrMarkingTag .twistedE6

@[expose] def GGSixLSixElevenKGRound8 : Prop :=
  GGOrdPInnerConjPSpNonsplit ∧ GGOrdPInnerConjPSUNonsplit ∧ GGOrdPInnerConjPOmegaPlusNonsplit ∧
    GGOrdPInnerConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPSpNonsplit ∧ GGOrdPFieldConjPSURest ∧ GGOrdPFieldConjPOmegaPlusRest ∧
    GGOrdPFieldConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧ GGOrdPTrialityInput

theorem ggSixLSixElevenKGRest8_of_round8 (h : GGSixLSixElevenKGRound8) :
    GGSixLSixElevenKGRest8 := by
  obtain ⟨hSp, hU, hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, hO2, hO3, hT⟩ := h
  exact ⟨hSp, hU, hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, ggOrdPOutdiagAt_PSU, hO2, hO3, hT⟩

end Lie

section Exc

theorem ggSixLSixElevenKGInput_of_round8 (h : GGSixLSixElevenKGRound8) :
    GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest8 (ggSixLSixElevenKGRest8_of_round8 h)

end Exc

section NonsplitCX

theorem ggSixLayerCXNonsplitInput_of_round8 (hα : GGNonsplitCompLiftRound8)
    (hβ : GGNonsplitNbrMarkingRound8) : GGSixLayerCXNonsplitInput :=
  ggSixLayerCXNonsplitInput_of_tags_PSL ggNonsplitTag_PSU_holds ggNonsplitTag_PSp_holds ⟨hα.1, hβ.1⟩
      ⟨hα.2.1, hβ.2.1⟩ ⟨hα.2.2.1, hβ.2.2.1⟩ ⟨hα.2.2.2.1, hβ.2.2.2.1⟩ ⟨hα.2.2.2.2.1, hβ.2.2.2.2.1⟩
      ⟨hα.2.2.2.2.2.1, hβ.2.2.2.2.2.1⟩ ⟨hα.2.2.2.2.2.2, hβ.2.2.2.2.2.2⟩

end NonsplitCX

end CFSG.StandardType
