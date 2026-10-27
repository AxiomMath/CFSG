module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusion
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOrth
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGLayerPDivRound6 : Prop :=
  GGLayerPDivTag .F4 ∧ GGLayerPDivTag .E6 ∧ GGLayerPDivTag .E7 ∧ GGLayerPDivTag .E8 ∧
    GGLayerPDivTag .twistedE6

theorem ggLayerPDivInput_of_round6 (h : GGLayerPDivRound6) : GGLayerPDivInput :=
  ggLayerPDivInput_of_remaining_five h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[expose] def GGInnerDiagStdRound6 : Prop :=
  GGInnerDiagStdE6 ∧ GGInnerDiagStdTwE6

end Lie

section HypSix

theorem ggInnerDiagMpInput_of_round6 (h : GGInnerDiagStdRound6) : GGInnerDiagMpInput :=
  ggInnerDiagMpInput_of_stdExc h.1 h.2

end HypSix

@[expose] def GGLayerCenterCyclicNonClassicalInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    LargeEvenSplit p lab → ¬ GGLayerClassicalLabel lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I)

@[expose] def GGLayerCenterCyclicRound6 : Prop :=
  GGLayerUnitaryModelInput ∧ GGLayerSymplecticModelInput ∧ GGLayerOmegaPlusModelInput ∧
    GGLayerOmegaMinusModelInput ∧ GGLayerCenterCyclicNonClassicalInput

theorem ggLayerCenterCyclicInput_of_round6
    (h : GGLayerCenterCyclicRound6) :
    GGLayerCenterCyclicInput :=
  ggLayerCenterCyclicInput_of_classical h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[expose] def GGTableBOtherRound6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBOtherRound5 p lab ∧ ¬ (lab.tag = .E6 ∧ p = 3)

theorem ggTableBOtherRound6_twE6 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBOtherRound6 p lab) (hs : LargeEvenSplit p lab) :
    lab.tag = .twE6 := by
  obtain ⟨⟨h4, hF4, hE6, hE78, hS⟩, hE3⟩ := h
  rcases ggTableBOtherRest4_cases hp hlab h4 hs with ht | ht | ht | ht | ht | ht |
    ⟨ht | ht | ht, -⟩
  · refine absurd ⟨ht, ?_⟩ hE3
    rcases (largeEvenSplit_E_iff (Or.inl ht)).mp hs with hd | hd
    · by_contra hp3
      exact hE6 ⟨ht, hd, hp3⟩
    · exact hd.2
  · exact ht
  · exact absurd (Or.inl ht) hS
  · exact absurd (Or.inr (Or.inl ht)) hS
  · exact absurd (Or.inr (Or.inr (Or.inl ht))) hS
  · exact absurd (Or.inr (Or.inr (Or.inr ht))) hS
  · exact absurd ⟨ht, hs⟩ hF4
  · exact absurd ⟨Or.inl ht, hs⟩ hE78
  · exact absurd ⟨Or.inr ht, hs⟩ hE78

section TableBE6

theorem ggBstarInputOn_round5_of_round6 (h : GGBstarInputOn GGTableBOtherRound6) :
    GGBstarInputOn GGTableBOtherRound5 :=
  (ggBstarInputOn_E6_three.or h).mono_split fun p lab hR hs => by
    by_cases hE : lab.tag = .E6 ∧ p = 3
    · exact Or.inl (ggTableBE6LabelThree_of_split hE.1 hE.2 hs)
    · exact Or.inr ⟨hR, hE⟩

@[expose] def GGTableBE6ThreeEndRound6 : Prop :=
  GGE6ThreeEndNodeInput ∧ GGE6TwoEndNodeInput

theorem ggStdSubPreInputOn_round5_of_round6 (hE : GGTableBE6ThreeEndRound6)
    (h : GGStdSubPreInputOn GGTableBOtherRound6) : GGStdSubPreInputOn GGTableBOtherRound5 :=
  ((ggStdSubPreInputOn_E6_three hE.1 hE.2).or h).mono_split fun p lab hR hs => by
    by_cases hE6 : lab.tag = .E6 ∧ p = 3
    · exact Or.inl (ggTableBE6LabelThree_of_split hE6.1 hE6.2 hs)
    · exact Or.inr ⟨hR, hE6⟩

theorem ggTableBSmallRankRound5_of_round6
    (h : TableBExcSmallRanks.GGTwF4ThreeRankInput) :
    GGTableBSmallRankRound5 :=
  ⟨TableBExcSmallRanks.ggTriD4ThreeRankInput_holds, TableBExcSmallRanks.ggTwF4RankInput_of_three h,
    TableBExcSmallRest.ggTitsThreeRankInput_holds⟩

end TableBE6

section TableB

theorem ggBstarInputOn_rest4_of_round6 (hS : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGBstarInputOn GGTableBOtherRound6) : GGBstarInputOn GGTableBOtherRest4 :=
  ggBstarInputOn_rest4_of_round5 (ggTableBSmallRankRound5_of_round6 hS)
    (ggBstarInputOn_round5_of_round6 h)

theorem ggStdSubPreInputOn_rest4_of_round6 (hE : GGTableBE6ThreeEndRound6)
    (hS : TableBExcSmallRanks.GGTwF4ThreeRankInput) (h : GGStdSubPreInputOn GGTableBOtherRound6) :
    GGStdSubPreInputOn GGTableBOtherRest4 :=
  ggStdSubPreInputOn_rest4_of_round5 TableBF4TwoInputs.ggF4TwoLocalEndNodeInput_holds
    TableBF4TwoInputs.ggF4TwoOuterRankInput_holds
    ⟨ggE7TwoRootFusionInput_holds, ggE8TwoRootFusionInput_holds⟩
    (ggTableBSmallRankRound5_of_round6 hS) (ggStdSubPreInputOn_round5_of_round6 hE h)

end TableB

@[expose] def GGTableBNbrInnerRound6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoRestLabel p lab ∧ ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1) ∧
    ¬ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∧
    ¬ GGTableBF4Label p lab

section NbrInner

theorem ggTableBNbrInnerInput_of_round6
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound6Label) : GGTableBNbrInnerInput :=
  ggTableBNbrInnerInput_of_rest_F4 h

end NbrInner

end CFSG.StandardType
