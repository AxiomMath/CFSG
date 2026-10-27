module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyFourDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFourTypeA
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFinal
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplit
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIsoAssembly
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperUnitaryLabel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmega
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFar
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestAssembly
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRest
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExc
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRest
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralClassical
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSUTag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Layer

@[expose] def GGLayerTagsRound5 : Prop :=
  GGExcAdjCoreRestInput .F4 ∧ GGExcAdjCoreRestInput .E7 ∧ GGExcAdjCoreRestInput .E8 ∧
    (GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6) ∧
    (GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6)

theorem ggLayerInputs_of_round5 (h : GGLayerTagsRound5) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_exc_rest h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

end Layer

section Exc

@[expose] def GGSixLSixElevenKGRound5 : Prop :=
  (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPInnerConjAt t) ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .PSU ∧ GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧
    GGOrdPGraphAt .POmegaPlus ∧ GGOrdPGraphAt .POmegaMinus ∧ GGOrdPTrialityInput

theorem ggSixLSixElevenKGInput_of_round5 (h : GGSixLSixElevenKGRound5) :
    GGSixLSixElevenKGInput := by
  obtain ⟨h1, h2, hU, hE6, hTw, hP, hM, h5⟩ := h
  refine ggSixLSixElevenKGInput_of_rest_PSL_holds h1 h2 ?_
    (fun t _ _ => ggOrdPGraphAt_of_orthogonal hP hM t) h5
  rintro t (rfl | rfl | rfl)
  exacts [hU, hE6, hTw]

end Exc

@[expose] def GGKGroupFusionRound5 : Prop :=
  GGAltNotMarkedInput ∧ GGLieParabolicCharInput ∧ GGLieOuterFieldAutInput ∧
    GGSeitzExcInputs ∧ GGKGroupFusionAt GGKFSporadic

section KFusion

open CFSG.LocalAnalysis.ComponentInitial CFSG.AGLEmbeddingD2 in
theorem ggKGroupFusionLayerInput_of_round5 (hSch : SchreierFor InCatalog)
    (hS : KFactSeitzRankTwo) (h : GGKGroupFusionRound5) : GGKGroupFusionLayerInput :=
  ggKGroupFusionLayerInput_of_seitzExcInputs hSch hS h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

end KFusion

section TableB

@[expose] def GGTableBSmallRankRound5 : Prop :=
  TableBExcSmallRest.GGTriD4ThreeRankInput ∧ TableBExcSmallRest.GGTwF4RankInput ∧
    TableBExcSmallRest.GGTitsThreeRankInput

@[expose] def GGTableBOtherRound5 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBOtherRest4 p lab ∧ ¬ GGTableBF4AllLabel p lab ∧ ¬ GGTableBE6LabelNotThree p lab ∧
    ¬ GGTableBE7E8AllLabel p lab ∧ ¬ TableBExcSmallRest.GGTableBExcSmallRestLabel p lab

theorem ggBstarInputOn_rest4_of_round5 (hS : GGTableBSmallRankRound5)
    (h : GGBstarInputOn GGTableBOtherRound5) : GGBstarInputOn GGTableBOtherRest4 :=
  ggBstarInputOn_rest4_of_noF4 <| ggBstarInputOn_rest4NoF4_of_noSmall hS.1 hS.2.1 hS.2.2 <|
    ggBstarInputOn_of_notE7E8All <|
    (ggBstarInputOn_E6_notThree.or h).mono_split fun p lab hl _ => by
      by_cases hE : GGTableBE6LabelNotThree p lab
      · exact Or.inl hE
      · exact Or.inr ⟨hl.1.1.1, hl.1.1.2, hE, hl.2, hl.1.2⟩

theorem ggStdSubPreInputOn_rest4_of_round5 (hE1 : TableBF4Two.GGF4TwoLocalEndNodeInput)
    (hE2 : TableBF4Two.GGF4TwoOuterRankInput) (hE78 : TableBExcTwo.GGE7TwoRootFusionInput ∧
        TableBExcTwo.GGE8TwoRootFusionInput)
    (hS : GGTableBSmallRankRound5) (h : GGStdSubPreInputOn GGTableBOtherRound5) :
    GGStdSubPreInputOn GGTableBOtherRest4 :=
  ggStdSubPreInputOn_rest4_of_noF4 hE1 hE2 <|
    ggStdSubPreInputOn_rest4NoF4_of_noSmall hS.1 hS.2.1 hS.2.2 <|
    ggStdSubPreInputOn_of_notE7E8All hE78.1 hE78.2 <|
    (ggStdSubPreInputOn_E6_notThree.or h).mono_split fun p lab hl _ => by
      by_cases hE : GGTableBE6LabelNotThree p lab
      · exact Or.inl hE
      · exact Or.inr ⟨hl.1.1.1, hl.1.1.2, hE, hl.2, hl.1.2⟩

end TableB

section Raw

@[expose] def GGRawInndiagIsoRound5 : Prop :=
  GGInndiagCommRestInput ∧ GGRawInndiagIsoExclInput

theorem ggRawInndiagIsoRestInput_of_round5 (h : GGRawInndiagIsoRound5) :
    GGRawInndiagIsoRestInput :=
  ggRawInndiagIsoRestInput_of_comm h.1 h.2

theorem ggRawPCyclicOn_notD4Three_of_round5
    (h : GGRawPCyclicOn fun p lab => GGNotD4Three p lab ∧ ¬ GGRawPCyclicDoneLabel lab ∧
      ¬ GGOmegaLabel lab) :
    GGRawPCyclicOn GGNotD4Three :=
  ggRawPCyclicOn_notD4Three_of_split ggRawPCyclicOn_done
    (((ggRawPCyclicOn_omega plusFourTrialityInput_holds).or h).mono fun p lab ⟨hne, hlab⟩ => by
      by_cases ho : GGOmegaLabel lab
      · exact Or.inl ⟨ho, hne⟩
      · exact Or.inr ⟨hne, hlab, ho⟩)

end Raw

section IOne


theorem ggStdSubIOneProperInput_of_round5 (ha₀ : GGLNoncyclicInput)
    (hR : GGStdSubIOneProperInputOn fun p lab => ¬ GGIOneUnitaryLabel p lab) :
    GGStdSubIOneProperInput :=
  ggStdSubIOneProperInput_of_cover ((ggStdSubIOneProperInputOn_unitary_holds ha₀).or hR)
    fun p lab _ _ => em (GGIOneUnitaryLabel p lab)

end IOne

section StepTwo

@[expose] def GGStepTwoToralRound5 : Prop :=
  GGStepTwoCoordModelOn .PSL ∧ GGStepTwoCoordModelOn .PSU ∧ GGStepTwoCoordModelOn .PSp ∧
    GGStepTwoCoordModelOn .POmegaPlus ∧ GGStepTwoCoordModelOn .POmegaMinus ∧
    GGStepTwoToralWitnessRestInput

theorem ggStepTwoCentralizerInput_of_round5 (h : GGStepTwoToralRound5) :
    GGStepTwoCentralizerInput :=
  ggStepTwoCentralizerInput_of_coordModels h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

end StepTwo

section PDiv

@[expose] def GGLayerPDivRound5 : Prop :=
  GGLayerPDivTag .POmegaPlus ∧ GGLayerPDivTag .POmegaMinus ∧ GGLayerPDivTag .F4 ∧
    GGLayerPDivTag .E6 ∧ GGLayerPDivTag .E7 ∧ GGLayerPDivTag .E8 ∧ GGLayerPDivTag .twistedE6

theorem ggLayerPDivInput_of_round5 (h : GGLayerPDivRound5) : GGLayerPDivInput :=
  ggLayerPDivInput_of_remaining_seven h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2

end PDiv

theorem ggTypeACompatFarExGenInput_iff_cfg :
    GGTypeACompatFarExGenInput ↔ GGTypeACompatFarExCfgInput :=
  Iff.rfl

theorem ggTypeACompatFarExGenInput_of_diag (hD : GGTypeACompatDiagInput)
    (hF : GGTypeABstarFarInput) (hO : GGBstarCentralizerOddInput) :
    GGTypeACompatFarExGenInput :=
  ggTypeACompatFarExGenInput_iff_cfg.mpr (ggTypeACompatFarExCfgInput_of_diag hD hF hO)

end CFSG.StandardType
