module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyNineDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOm
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSUDelta
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpCont
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelURound8
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlk
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGSixLSixElevenKGRound10 : Prop :=
  (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPOmegaPlusRest ∧ GGOrdPFieldConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧ GGOrdPTrialityInput

theorem ggSixLSixElevenKGRound10_of_round9 (h : GGSixLSixElevenKGRound9) :
    GGSixLSixElevenKGRound10 := by
  obtain ⟨-, -, hI, -, -, hFOP, hFOM, hF, hO2, hO3, hT⟩ := h
  exact ⟨hI, hFOP, hFOM, hF, hO2, hO3, hT⟩

theorem ggSixLSixElevenKGRound9_of_round10 (h : GGSixLSixElevenKGRound10) :
    GGSixLSixElevenKGRound9 := by
  obtain ⟨hI, hFOP, hFOM, hF, hO2, hO3, hT⟩ := h
  exact ⟨ggOrdPInnerConjPOmegaPlusNonsplit_holds, ggOrdPInnerConjPOmegaMinusNonsplit_holds, hI,
    ggOrdPFieldConjPSpNonsplit_holds, ggOrdPFieldConjPSURest_holds, hFOP, hFOM, hF, hO2, hO3, hT⟩

@[expose] def GGStepTwoToralRound10 : Prop :=
  GGSUPieceSwapInput ∧ GGSUPieceShapeInput ∧ GGStepTwoCoordModelOn .POmegaPlus ∧
    GGStepTwoCoordModelOn .POmegaMinus ∧ GGStepTwoToralWitnessRestInput

theorem ggStepTwoToralRound8_of_round10 (h : GGStepTwoToralRound10) : GGStepTwoToralRound8 :=
  ggStepTwoToralRound8_of_piece ggSpCoordModelNonsplitInput_holds h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2

@[expose] def GGSixRootFusionWitClRound10 : Prop :=
  GGSixRootFusionWitOmPlusQ1 ∧ GGSixRootFusionWitOmPlusRest ∧ GGSixRootFusionWitOmMinusQ1 ∧
    GGSixRootFusionWitOmMinusRest

theorem ggSixRootFusionWitClRound10_of_round9 (h : GGSixRootFusionWitClRound9) :
    GGSixRootFusionWitClRound10 :=
  h.2.2

theorem ggSixRootFusionWitnessInputFor_otherClassical_of_round10
    (h : GGSixRootFusionWitClRound10) : GGSixRootFusionWitnessInputFor GGOtherClassicalTag :=
  ggSixRootFusionWitnessInputFor_otherClassical_of_omega
    (ggSixRootFusionWitnessOn_POmegaPlus_of_parts h.1 h.2.1)
    (ggSixRootFusionWitnessOn_POmegaMinus_of_parts h.2.2.1 h.2.2.2)

end Lie

section FieldFive

@[expose] def GGSixFieldFiveRound10 : Prop :=
  GGFieldFiveNbrTag .POmegaPlus ∧ GGFieldFiveNbrTag .POmegaMinus ∧ GGFieldFiveNbrTag .E8

theorem ggSixFieldFiveInput_of_round10 (h : GGSixFieldFiveRound10) : GGSixFieldFiveInput :=
  ggSixFieldFiveInput_of_omega_e8 h.1 h.2.1 h.2.2

end FieldFive

end CFSG.StandardType
