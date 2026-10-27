module

public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenPAS
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPHinge
public import CFSG.LocalAnalysis.WeakClosure81.EightTwentyP
public import CFSG.LocalAnalysis.WeakClosure81.EightEight
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveAS
public import CFSG.LocalAnalysis.WeakClosure81.EightNVHoldsAS
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoBridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapsDischarged
import CFSG.RepresentationTheory.SL2NatSum.NatSumInput
import CFSG.RepresentationTheory.SzMartineau.MartineauInput
public import CFSG.LocalAnalysis.WeakClosure81.EightEleven
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1 W3Thm88)

variable {G : Type} [Group G] [Finite G]

theorem Sit813.false''_AS (hin : W3In814 G) (hc819 : W3Claim819' G) (hc820 : W3Claim820' G)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : False := by
  rcases h.concl813.eShapeP.cases with hAB | hUC
  · exact h.eight_nineteen'_AS hin hc819 h5_11 h5_13 hAB
  · exact h.eight_twenty' hin hc820 hUC

theorem not_minCex88'_AS (hin : W3In814 G) (hc813 : W3Lem813'' G)
    (hc819 : W3Claim819' G) (hc820 : W3Claim820' G) (h861 : W3Lem86_1 G) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) {V H T : Subgroup G} {i : ℕ} : ¬ MinCex88 V H T i := by
  intro h
  obtain ⟨A, hA, hAO, x, hx, hxM⟩ := h.hyp.exists_gammaSet_not_le_normalizer
  have h812 := h.eight_twelve_AS h861 h5_11 h5_13 hA hAO
  have hH0 : IsCalH0 V H := ⟨h.hyp.calH, MinCex88.le_pCoreOf_AS h861 h5_11 h5_13 h⟩
  obtain ⟨L, K, h813⟩ := h.eight_thirteen'' hc813 hH0 hA ⟨x, hx, hxM⟩ h812
  exact (Sit813.ofP h hH0 hA ⟨x, hx, hxM⟩ h812 h813).false''_AS hin hc819 hc820 h5_11 h5_13

theorem eight_eight'_AS (hin : W3In814 G) (hc813 : W3Lem813'' G)
    (hc819 : W3Claim819' G) (hc820 : W3Claim820' G) (h861 : W3Lem86_1 G) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) {V H T : Subgroup G} (hV7 : Hyp7 V) (hH : IsCalH V H)
    (hK : CFSG.Open.IsKGroup ↥H)
    (hT : IsSylowIn 2 T (H ⊓ normalizer (V : Set G))) (ha : E3.wClos V 0 T ≠ V)
    (hb : 2 < rk ↥V) (hc : ¬ H ≤ normalizer (V : Set G))
    (hd : ∃ i : ℕ, i ≤ 1 ∧ H ⊓ normalizer (E3.wClos V i T : Set G) ≤ normalizer (V : Set G))
    (he : CentralizersInM V H T) : Concl881 V H ∧ Concl882 V H := by
  by_contra hfail
  obtain ⟨i, hi, hd'⟩ := hd
  obtain ⟨H', T', i', hmin⟩ := exists_minCex88_of_not_concl
    ⟨hV7, hH, hK, hT, ha, hb, hc, hi, hd', he⟩ hfail
  exact not_minCex88'_AS hin hc813 hc819 hc820 h861 h5_11 h5_13 hmin

theorem w3Thm88_holds'_AS (hin : W3In814 G) (hc813 : W3Lem813'' G)
    (hc819 : W3Claim819' G) (hc820 : W3Claim820' G) (h861 : W3Lem86_1 G) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) : W3Thm88 G :=
  fun {_ _ _ i} h => eight_eight'_AS hin hc813 hc819 hc820 h861 h5_11 h5_13 h.hyp7 h.calH
    h.kgroup h.sylow h.wne h.rank h.notLe ⟨i, h.i_le, h.normW⟩ h.centr

section Split

theorem w3Thm88_of_split_claims'_discharged_AS_at3
    (hc813 : W3Lem813'' G) (hc819 : W3Claim819' G) (hc820 : W3Claim820' G)
    (hTim : TimmesfeldTIRootInput)
    (hGen : TwoConjugateGeneration)
    (hA6 : ∀ (K : Type) [Group K] [Finite K], SevenElevenASixInput K)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (h772 : ∀ (K : Type) [Group K] [Finite K], SevenSevenTwoInput K)
    (hIn : OrthReflParabolic) (hRU : UnitaryRootCommutatorRankAt 3)
    (hRL : L2RootCommutatorRank)
    (hfact : Orth6MinusOddTranspFact)
    (h85three : W3Lem85ThreeFirst G) (hsh : W3Shape86C G)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) : W3Thm88 G :=
  w3Thm88_holds'_AS
    (w3In814_of_inputs_AS
      (w3Lem122One_holds CFSG.RepresentationTheory.SL2NatSum.natSumL2Input_holds
        CFSG.RepresentationTheory.SzMartineau.martineauSzInput_holds)
      w3Lem122Two_holds h5_11 h5_13)
    hc813 hc819 hc820
    (w3Lem86_1_of_split_inputs_at3
      (w3Lem711Alt_subgroups_of_inputs hTim hGen hA6 hCore hList h772 hIn) hRU hRL hfact
      h85three hsh)
    h5_11 h5_13

theorem w3Thm88_of_split_claims'_discharged_AS
    (hc813 : W3Lem813'' G) (hc819 : W3Claim819' G) (hc820 : W3Claim820' G)
    (hTim : TimmesfeldTIRootInput)
    (hGen : TwoConjugateGeneration)
    (hA6 : ∀ (K : Type) [Group K] [Finite K], SevenElevenASixInput K)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (h772 : ∀ (K : Type) [Group K] [Finite K], SevenSevenTwoInput K)
    (hIn : OrthReflParabolic) (hRU : UnitaryRootCommutatorRank) (hRL : L2RootCommutatorRank)
    (hfact : Orth6MinusOddTranspFact)
    (h85three : W3Lem85ThreeFirst G) (hsh : W3Shape86C G)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) : W3Thm88 G :=
  w3Thm88_of_split_claims'_discharged_AS_at3 hc813 hc819 hc820 hTim hGen hA6 hCore hList h772
    hIn (unitaryRootCommutatorRank_iff_at.1 hRU 3 le_rfl) hRL hfact h85three hsh h5_11 h5_13

end Split

end CFSG.LocalAnalysis.WeakClosure81

end
