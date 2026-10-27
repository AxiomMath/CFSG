module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUPSU
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRest
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoEndNode
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestMain
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphAssembly
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenCases
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGOppositeRadicalRest4 : Prop :=
  GGOppositeRadicalCountNormalAt .POmegaPlus ∧ GGOppositeRadicalCountNormalAt .POmegaMinus ∧
    GGOppositeRadicalCountNormalAt .F4 ∧ GGOppositeRadicalCountNormalAt .E6 ∧
    GGOppositeRadicalCountNormalAt .E7 ∧ GGOppositeRadicalCountNormalAt .E8 ∧
    GGOppositeRadicalCountNormalAt .twistedE6

theorem ggOppositeRadicalCountNormalInput_of_rest4 (h : GGOppositeRadicalRest4) :
    GGOppositeRadicalCountNormalInput :=
  ggOppositeRadicalCountNormalInput_of_families'' h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2

@[expose] def GGLayerTagsRest4 : Prop :=
  (GGLayerCentreOddTag .POmegaPlus ∧ GGLayerPerfectTag .POmegaPlus) ∧
    (GGLayerCentreOddTag .POmegaMinus ∧ GGLayerPerfectTag .POmegaMinus) ∧
    (GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4) ∧
    (GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6) ∧
    (GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7) ∧
    (GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8) ∧
    (GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6)

theorem ggLayerInputs_of_rest4 (h : GGLayerTagsRest4) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_remaining_seven h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2

@[expose] def GGSixSeventeenWitnessRest4 : Prop :=
  GGSixSeventeenLinearWitnessInput ∧ GGSixSeventeenE8SevenInput ∧
    GGSixSeventeenRootWitnessInputFor GGOtherClassicalTag ∧
    GGSixSeventeenRootWitnessInputFor GGExceptionalTag

theorem ggSixSeventeenWitnessInput_of_rest4 (h : GGSixSeventeenWitnessRest4) :
    GGSixSeventeenWitnessInputFor fun _ => True :=
  ggSixSeventeenWitnessInput_of_cases h.1 h.2.1 h.2.2.1 h.2.2.2

@[expose] def GGSecFiveWeylRest4 : Prop :=
  GGSecFiveWeylAInput ∧ GGSecFiveWeylBRestInput ∧ GGSecFiveWeylDInput ∧ GGSecFiveWeylEInput ∧
    GGSecFiveWeylF4Input ∧ GGSecFiveWeylG2Input

theorem ggSecFiveDataInputRest_of_rest4 (hNW : GGSecFiveNonWeylInput)
    (hE : GGTypeAJoinEndNodeInput) (hC : GGTypeACorankTwoInput) (hH : GGTypeAHalfEndNodesInput)
    (hL : GGSpLiftInput) (hSE : GGSpJoinEndNodeInput) (hSJ : GGSpJoinInput)
    (h : GGSecFiveWeylRest4) : GGSecFiveDataInputRest :=
  ggSecFiveDataInputRest_of_cases hNW hE hC hH h.1 (ggSecFiveWeylBInput_of_typeC hL hSE hSJ h.2.1)
    h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

end Lie

section Exc

@[expose] def GGSixLSixElevenKGRest4 : Prop :=
  GGOrdPInnerConjPSLNonsplit ∧ GGOrdPFieldConjPSLNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPInnerConjAt t) ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .PSU ∧ GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧
    GGOrdPGraphAt .POmegaPlus ∧ GGOrdPGraphAt .POmegaMinus ∧ GGOrdPTrialityInput

theorem ggSixLSixElevenKGInput_of_rest4 (h : GGSixLSixElevenKGRest4) :
    GGSixLSixElevenKGInput := by
  obtain ⟨hK1, hK2, h1, h2, hU, hE6, hTw, hP, hM, h5⟩ := h
  refine ggSixLSixElevenKGInput_of_rest_PSL hK1 hK2 h1 h2 ?_
    (fun t _ _ => ggOrdPGraphAt_of_orthogonal hP hM t) h5
  rintro t (rfl | rfl | rfl)
  exacts [hU, hE6, hTw]

end Exc

@[expose] def GGKGroupFusionRest4 : Prop :=
  GGAltNotMarkedInput ∧ GGLieParabolicCharInput ∧ GGLieOuterFieldAutInput ∧
    GGKGroupFusionAt GGKFLieSeitzException ∧ GGKGroupFusionAt GGKFSporadic

open CFSG.LocalAnalysis.ComponentInitial CFSG.AGLEmbeddingD2 in
theorem ggKGroupFusionLayerInput_of_rest4 (hSch : SchreierFor InCatalog)
    (hS : KFactSeitzRankTwo) (h : GGKGroupFusionRest4) : GGKGroupFusionLayerInput :=
  ggKGroupFusionLayerInput_of_reduced hSch hS h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2


section F4

@[expose] def GGTableBOtherRest4NoF4 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBOtherRest4 p lab ∧ ¬ GGTableBF4AllLabel p lab

theorem ggBstarInputOn_rest4_of_noF4 (h : GGBstarInputOn GGTableBOtherRest4NoF4) :
    GGBstarInputOn GGTableBOtherRest4 :=
  (ggBstarInputOn_F4_all.or h).mono fun p lab _ _ hl => by
    by_cases hF : GGTableBF4AllLabel p lab
    exacts [Or.inl hF, Or.inr ⟨hl, hF⟩]

theorem ggStdSubPreInputOn_rest4_of_noF4 (hE1 : TableBF4Two.GGF4TwoLocalEndNodeInput)
    (hE2 : TableBF4Two.GGF4TwoOuterRankInput) (h : GGStdSubPreInputOn GGTableBOtherRest4NoF4) :
    GGStdSubPreInputOn GGTableBOtherRest4 :=
  ((ggStdSubPreInputOn_F4_all_of_inputs hE1 hE2).or h).mono fun p lab _ _ hl => by
    by_cases hF : GGTableBF4AllLabel p lab
    exacts [Or.inl hF, Or.inr ⟨hl, hF⟩]

end F4

end CFSG.StandardType
