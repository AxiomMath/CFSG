module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyEightDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitRest
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmRound8
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmTag
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmRest
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsComp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGSixLSixElevenKGRound9 : Prop :=
  GGOrdPInnerConjPOmegaPlusNonsplit ∧ GGOrdPInnerConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPSpNonsplit ∧ GGOrdPFieldConjPSURest ∧ GGOrdPFieldConjPOmegaPlusRest ∧
    GGOrdPFieldConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧ GGOrdPTrialityInput

theorem ggSixLSixElevenKGRound9_of_round8 (h : GGSixLSixElevenKGRound8) :
    GGSixLSixElevenKGRound9 := by
  obtain ⟨-, -, hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, hO2, hO3, hT⟩ := h
  exact ⟨hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, hO2, hO3, hT⟩

theorem ggSixLSixElevenKGRest9_of_round9 (h : GGSixLSixElevenKGRound9) :
    GGSixLSixElevenKGRest9 := by
  obtain ⟨hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, hO2, hO3, hT⟩ := h
  exact ⟨hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, ggOrdPOutdiagAt_PSU, hO2, hO3, hT⟩

@[expose] def GGStepTwoToralRound9 : Prop :=
  GGSpNsZeroContInput ∧ GGSpNsClassContInput ∧ GGStepTwoCoordModelOn .PSU ∧
    GGStepTwoCoordModelOn .POmegaPlus ∧ GGStepTwoCoordModelOn .POmegaMinus ∧
    GGStepTwoToralWitnessRestInput

theorem ggStepTwoToralRound8_of_round9 (h : GGStepTwoToralRound9) : GGStepTwoToralRound8 :=
  ⟨ggSpCoordModelNonsplitInput_of_cont h.1 h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

@[expose] def GGLayerNotDFourTwoRound9 : Prop :=
  GGLayerNotDFourTwoTag .F4 ∧ GGLayerNotDFourTwoTag .E6 ∧ GGLayerNotDFourTwoTag .E7 ∧
    GGLayerNotDFourTwoTag .E8 ∧ GGLayerNotDFourTwoTag .twistedE6

@[expose] def GGLayerNotUFourAltSixRound9 : Prop :=
  GGLayerNotUFourAltSixTag .F4 ∧ GGLayerNotUFourAltSixTag .E6 ∧ GGLayerNotUFourAltSixTag .E7 ∧
    GGLayerNotUFourAltSixTag .E8 ∧ GGLayerNotUFourAltSixTag .twistedE6

theorem ggLayerNotDFourTwoRound9_of_round7 (h : GGLayerNotDFourTwoRound7) :
    GGLayerNotDFourTwoRound9 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem ggLayerNotUFourAltSixRound9_of_rest (h : GGLayerNotUFourAltSixRest) :
    GGLayerNotUFourAltSixRound9 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem ggStepTwoAutKRestInput_of_round9 (h3 : GGAutKCanonIIIInput) (h4 : GGAutKCanonIVInput)
    (hF : GGSixFieldFiveInput) (hD : GGLayerNotDFourTwoRound9) (hU : GGLayerNotUFourAltSixRound9)
    (h2 : GGStepTwoChoiceThreeTwoRest) : GGStepTwoAutKRestInput :=
  ggStepTwoAutKRestInput_of_last_exc h3 h4 hF hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2 hU.1
    hU.2.1 hU.2.2.1 hU.2.2.2.1 hU.2.2.2.2 h2

@[expose] def GGNonsplitCompLiftRound9 : Prop :=
  GGNonsplitCompLiftTag .F4 ∧ GGNonsplitCompLiftTag .E6 ∧ GGNonsplitCompLiftTag .E7 ∧
    GGNonsplitCompLiftTag .E8 ∧ GGNonsplitCompLiftTag .twistedE6

@[expose] def GGNonsplitNbrMarkingRound9 : Prop :=
  GGNonsplitNbrMarkingTag .F4 ∧ GGNonsplitNbrMarkingTag .E6 ∧ GGNonsplitNbrMarkingTag .E7 ∧
    GGNonsplitNbrMarkingTag .E8 ∧ GGNonsplitNbrMarkingTag .twistedE6

theorem ggNonsplitCompLiftRound9_of_round8 (h : GGNonsplitCompLiftRound8) :
    GGNonsplitCompLiftRound9 :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem ggNonsplitNbrMarkingRound9_of_round8 (h : GGNonsplitNbrMarkingRound8) :
    GGNonsplitNbrMarkingRound9 :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

@[expose] def GGSixRootFusionWitClRound9 : Prop :=
  GGSpBlockWitnessInputOn (fun _ f p => ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1) ∧
    SpBlockFixOrSwapInput ∧ GGSixRootFusionWitOmPlusQ1 ∧ GGSixRootFusionWitOmPlusRest ∧
    GGSixRootFusionWitOmMinusQ1 ∧ GGSixRootFusionWitOmMinusRest

theorem ggSixRootFusionWitClRound9_of_rest2_restOm (h₁ : GGSixRootFusionWitClRest2)
    (h₂ : GGSixRootFusionWitClRestOm) : GGSixRootFusionWitClRound9 :=
  ⟨h₁.1, h₁.2.1, h₂.2.2⟩

theorem ggSixRootFusionWitClRestOm_of_round9 (h : GGSixRootFusionWitClRound9) :
    GGSixRootFusionWitClRestOm := by
  obtain ⟨hblk, hF, hPQ, hPR, hMQ, hMR⟩ := h
  exact ⟨ggSpPlaneWitnessInputOn_nonsplit,
    (ggSixRootFusionWitnessOn_PSp_of_blockWitness hblk hF).mono fun _ _ _ _ ht => ht,
    hPQ, hPR, hMQ, hMR⟩

end Lie

section Exc

theorem ggSixLSixElevenKGInput_of_round9 (h : GGSixLSixElevenKGRound9) :
    GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest9 (ggSixLSixElevenKGRest9_of_round9 h)

end Exc

section NonsplitCX

theorem ggSixLayerCXNonsplitInput_of_round9 (hα : GGNonsplitCompLiftRound9)
    (hβ : GGNonsplitNbrMarkingRound9) : GGSixLayerCXNonsplitInput :=
  ggSixLayerCXNonsplitInput_of_tags_exc ⟨hα.1, hβ.1⟩ ⟨hα.2.1, hβ.2.1⟩ ⟨hα.2.2.1, hβ.2.2.1⟩
    ⟨hα.2.2.2.1, hβ.2.2.2.1⟩ ⟨hα.2.2.2.2, hβ.2.2.2.2⟩

end NonsplitCX

end CFSG.StandardType
