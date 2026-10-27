module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTenDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOmPlusFourField
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmField
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityEightRest
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUInRound
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralRestTags
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMoves
public import CFSG.LocalAnalysis.StandardType.GGRootPlaneD4
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmall
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenE8Seven
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvd
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNs
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVacMore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGTableBNbrInnerRound11NsLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound11Label p lab ∧ ¬ GGOrthNsLabel p lab

@[expose] def GGCorFourTwoOpenTableBRound11Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenTableBVacRest3Label p lab ∧ ¬ GGOrthNsVacLabel p lab

@[expose] def GGCorFourTwoOpenLineRound11Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLineRest3Label p lab ∧ ¬ GGOrthNsLabel p lab

theorem ggTableBNbrInnerInputOn_round11Ns_of_round11
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound11Label) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound11NsLabel :=
  h.mono fun _ _ h => h.1

theorem ggTableBCxInputOn_round11_of_rest3
    (h : GGTableBCxInputOn GGCorFourTwoOpenTableBVacRest3Label) :
    GGTableBCxInputOn GGCorFourTwoOpenTableBRound11Label :=
  h.mono fun _ _ h => h.1

theorem ggTableBModuleInputOn_round11_of_rest3
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBVacRest3Label) :
    GGTableBModuleInputOn GGCorFourTwoOpenTableBRound11Label :=
  h.mono fun _ _ h => h.1

theorem ggTableBActionInputOn_round11_of_rest3
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBVacRest3Label) :
    GGTableBActionInputOn GGCorFourTwoOpenTableBRound11Label :=
  h.mono fun _ _ h => h.1

theorem ggLNoInvariantLineInputOn_round11_of_rest3
    (h : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRest3Label) :
    GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRound11Label :=
  CorFourTwoVacMore.lNoInvariantLineInputOn_mono (fun _ _ h => h.1) h

section LabelDropIns


theorem ggLNoInvariantLineInputOn_rest3_of_round11
    (h : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRound11Label) :
    GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRest3Label :=
  ggLNoInvariantLineInputOn_of_not_orthNs (S := GGCorFourTwoOpenLineRest3Label) h

theorem ggTableBNbrInnerInputOn_round11_of_round11Ns
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound11NsLabel) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound11Label :=
  ggTableBNbrInnerInputOn_of_not_orthNs (S := GGTableBNbrInnerRound11Label) h

end LabelDropIns

section Lie

@[expose] def GGSixLSixElevenKGRound11 : Prop :=
  (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPInnerConjAt t) ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧ GGD4GraphFieldLayerInput ∧
    GGD4GraphLayerInput

theorem ggSixLSixElevenKGRound10_of_round11 (h : GGSixLSixElevenKGRound11) :
    GGSixLSixElevenKGRound10 := by
  obtain ⟨hI, hF, hO2, hO3, hGF, hG⟩ := h
  exact ⟨hI, ggOrdPFieldConjPOmegaPlusRest_holds, ggOrdPFieldConjPOmegaMinusNonsplit_holds, hF, hO2,
    hO3, ggOrdPTrialityInput_of_rest_layers ggOrdPFieldConjPOmegaPlusRest_holds hGF hG⟩

@[expose] def GGStepTwoToralRound11 : Prop :=
  GGOmFrameElemMoveInput ∧ GGStepTwoToralWitnessOn .F4 ∧ GGStepTwoToralWitnessOn .E6 ∧
    GGStepTwoToralWitnessOn .E7 ∧ GGStepTwoToralWitnessOn .E8 ∧
    GGStepTwoToralWitnessOn .twistedE6

theorem ggStepTwoToralRound8_of_round11 (h : GGStepTwoToralRound11) : GGStepTwoToralRound8 := by
  obtain ⟨hElem, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ggStepTwoToralRound8_of_rest ggSpCoordModelNonsplitInput_holds
    (ggStepTwoCoordModelOn_POmegaPlus_of_elem hElem)
    (ggStepTwoCoordModelOn_POmegaMinus_of_elem hElem)
    (ggStepTwoToralWitnessRestInput_of_exc hF4 hE6 hE7 hE8 hTwE6)

@[expose] def GGRootPlaneExcRound11 : Prop :=
  GGRootPlaneAt .F4 ∧ GGRootPlaneAt .E6 ∧ GGRootPlaneAt .E7 ∧ GGRootPlaneAt .E8 ∧
    GGRootPlaneAt .twistedE6

theorem ggRootPlaneExcRound11_of_d4Exc (h : GGRootPlaneRestD4Exc) : GGRootPlaneExcRound11 :=
  h.2

theorem ggRootPlaneRestD4Exc_of_round11 (h : GGRootPlaneExcRound11) : GGRootPlaneRestD4Exc :=
  ggRootPlaneRestD4Exc_of_exc h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[expose] def GGRootCentSummandStructRound11 : Prop :=
  GGRootCentDerivedTag .PSU ∧ GGRootCentLayerTag .PSp ∧ GGRootCentLayerTag .POmegaPlus ∧
    GGRootCentLayerTag .POmegaMinus ∧ GGRootCentDerivedTag .F4 ∧ GGRootCentDerivedTag .E6 ∧
    GGRootCentDerivedTag .E7 ∧ GGRootCentDerivedTag .E8 ∧ GGRootCentDerivedTag .twistedE6

theorem ggRootCentSummandStructInput_of_round11 (h : GGRootCentSummandStructRound11) :
    GGRootCentSummandStructInput := by
  obtain ⟨hPSU, hPSp, hPlus, hMinus, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ggRootCentSummandStructInput_of_nineTags hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6

end Lie

section Nonsplit

@[expose] def GGNonsplitCoreRound11 : Prop :=
  GGExcNonsplitCoreInput .F4 ∧ GGE6NonsplitCoreInput ∧ GGExcNonsplitCoreInput .E7 ∧
    GGExcNonsplitCoreInput .E8 ∧ GGNonsplitTag .twistedE6

theorem ggSixLayerCXNonsplitInput_of_round11 (h : GGNonsplitCoreRound11) :
    GGSixLayerCXNonsplitInput := by
  obtain ⟨hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ggSixLayerCXNonsplitInput_of_excCoreSix hF4 hE6 hE7 hE8 hTwE6

end Nonsplit

section Seventeen

@[expose] def GGSixSeventeenWitnessRound11 : Prop :=
  GGSixSeventeenE8SevenCentInput ∧ GGSixSeventeenRootWitnessInputFor GGExceptionalTag

theorem ggSixSeventeenWitnessRest12_of_round11 (h : GGSixSeventeenWitnessRound11) :
    GGSixSeventeenWitnessRest12 :=
  ⟨ggSixSeventeenE8SevenInput_of_cent h.1, h.2⟩

end Seventeen

end CFSG.StandardType
