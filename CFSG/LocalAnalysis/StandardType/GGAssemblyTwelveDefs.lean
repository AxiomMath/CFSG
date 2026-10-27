module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyElevenDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3Proof
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvMoves
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSpTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6ThreeRound

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGSixLSixSevenConjA3Round12 : Prop :=
  GGSixLSixSevenConjA3At .PSL ∧ GGSixLSixSevenConjA3At .POmegaPlus ∧ GGSixLSixSevenConjA3At .E6 ∧
    GGSixLSixSevenConjA3RestSeven

theorem ggSixLSixSevenConjA3Input_of_round12 (h : GGSixLSixSevenConjA3Round12) :
    GGSixLSixSevenConjA3Input :=
  ggSixLSixSevenConjA3Input_of_rest h.1 h.2.1 h.2.2.1 h.2.2.2

@[expose] def GGStepTwoToralRound12 : Prop :=
  GGStepTwoToralWitnessOn .F4 ∧ GGStepTwoToralWitnessOn .E6 ∧ GGStepTwoToralWitnessOn .E7 ∧
    GGStepTwoToralWitnessOn .E8 ∧ GGStepTwoToralWitnessOn .twistedE6

theorem ggStepTwoToralRound11_of_round12 (h : GGStepTwoToralRound12) : GGStepTwoToralRound11 :=
  ⟨ggOmFrameElemMoveInput_holds, h⟩

end Lie

section TwE6

@[expose] def GGTableBTwE6Round12 : Prop :=
  GGTwE6FieldCentInvInput ∧ GGTwE6ThreeInndiagRankInput ∧ GGTwE6ThreeCoverRankInput ∧
    GGTwE6ThreeDeltaTwoInput ∧ GGTwE6ThreeRootKernelInput ∧ GGTwE6ThreeFieldInput ∧
    GGTwE6EndNodeInnerInput ∧ GGTwE6EndNodeThreeInput

theorem ggBstarInputOn_round6_of_round12 (h : GGTableBTwE6Round12) :
    GGBstarInputOn GGTableBOtherRound6 := by
  obtain ⟨hF, hX, hC, hD, hB1, hB2, -, -⟩ := h
  exact ggBstarInputOn_round6_of_twE6Inputs hF hX hC hD hB1 hB2

theorem ggStdSubPreInputOn_round6_of_round12
    (h : GGTableBTwE6Round12) : GGStdSubPreInputOn GGTableBOtherRound6 := by
  obtain ⟨-, -, -, -, -, -, hI, hE3⟩ := h
  exact ggStdSubPreInputOn_round6_of_twE6Inputs hI hE3

end TwE6

section Inner

@[expose] def GGSixLSixElevenKGRound12 : Prop :=
  GGOrdPToralF4Rest ∧ GGOrdPToralE6Rest ∧ GGOrdPToralE7Rest ∧ GGOrdPToralE8Rest ∧
    GGTwE6InndiagOrdPInnerInput ∧ GGTwE6CenterTrivialInput ∧ GGOrdPToralTwE6Input ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧ GGD4GraphFieldLayerInput ∧
    GGD4GraphLayerInput

theorem ggSixLSixElevenKGRound11_of_round12 (h : GGSixLSixElevenKGRound12) :
    GGSixLSixElevenKGRound11 := by
  obtain ⟨hF4, hE6, hE7, hE8, hI, hZ, hT, hF, hO2, hO3, hGF, hG⟩ := h
  exact ⟨ggOrdPInnerConjExc_of_rest ⟨hF4, hE6, hE7, hE8, hI, hZ, hT⟩, hF, hO2, hO3, hGF, hG⟩

end Inner

end CFSG.StandardType
