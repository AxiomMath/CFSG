module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Cross
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329InChar3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15UnitaryEndgame
public import CFSG.Holt.PointHullTwoGroupBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel classicalTags chevalleyExceptionalTags reeTitsTags)
open CFSG.Open (StatedLieTag)

theorem k329lie_tag_mem_classical (S : Type) [Group S] (t : StatedLieTag) (n p f : ℕ)
    (h : CFSG.Open.StatedClassicalModel S t n p f) : t ∈ classicalTags := by
  cases t <;> first | exact h.2.elim | simp [classicalTags]

theorem k329LieTypeStatement_holds
    : k329LieTypeStatement := by
  intro G _ _ hQ hK hm3 X hXK hX
  set K : Subgroup G := CFSG.Open.genFittingFStar G with hKdef
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXs : IsSimpleGroup ↥X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hX
  have hcardX : Nat.card ↥X = 5515776 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  have hXnc : ∃ a b : ↥X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative ↥X := IsMulCommutative.of_comm fun a b => hcon a b
    have hp := (@Group.is_simple_iff_prime_card ↥X _ hcomm).mp hXs
    rw [hcardX] at hp
    exact (by norm_num : ¬ (5515776 : ℕ).Prime) hp
  have hXq : CFSG.Open.IsQuasisimple ↥X :=
    CFSG.Holt.PointHull.isQuasisimple_of_isSimpleGroup hXnc
  have h5 : 5515776 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.unitary_order_dvd_center_quotient hXK hXq hX
  have h19 : 19 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := (by norm_num : 19 ∣ 5515776).trans h5
  have hSs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hQ.2
  have hSnc : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative (↥K ⧸ Subgroup.center ↥K) :=
      IsMulCommutative.of_comm fun a b => hcon a b
    have hp := (@Group.is_simple_iff_prime_card _ _ hcomm).mp hSs
    rcases (Nat.dvd_prime hp).mp h5 with h | h
    · norm_num at h
    · rw [← h] at hp
      exact (by norm_num : ¬ (5515776 : ℕ).Prime) hp
  have hr : CFSG.Open.pRank 3 K ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top).trans hm3
  have hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
    KCore.KGroupNonab.catalogue_self CFSG.Open.isCatalogGroup_isoInvariant hK hSnc
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center ↥K)
  · exfalso
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 X
    have hKr3 : 3 ≤ CFSG.Open.pRank 3 K :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.three_le_pRank_of_unitary_three_center
        hXK hXq hX hP hZ
    have hK3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact Nat.le_antisymm hr hKr3
    have hON :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k34odd_threeCover_of_three_dvd
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
        CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
        K hQ hcat hZ hK3
    obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel
      (hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
    obtain ⟨a, ha⟩ :=
      CFSG.RankThree.PartTwo.Sec14.Ronan148H.exists_orderOf_nine_projSU_three_eight
    let x : ↥K := Subgroup.inclusion hXK (e.symm a)
    have hx : orderOf x = 9 := by
      calc orderOf x = orderOf (x : G) := (Subgroup.orderOf_coe x).symm
        _ = orderOf ((e.symm a : ↥X) : G) := rfl
        _ = orderOf (e.symm a) := Subgroup.orderOf_coe _
        _ = orderOf a := e.symm.orderOf_eq _
        _ = 9 := ha
    have hpg : IsPGroup 3 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
    obtain ⟨T, hT⟩ := hpg.exists_le_sylow
    have hx3 : x ^ 3 = 1 :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
        K hON T x (hT (Subgroup.mem_zpowers x))
    have hdiv := orderOf_dvd_of_pow_eq_one hx3
    rw [hx] at hdiv
    norm_num at hdiv
  · have hrS : CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K)) ≤ 3 := by
      rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center ↥K) hZ,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact hr
    have hCat : CFSG.Blueprint.Catalog (↥K ⧸ Subgroup.center ↥K) :=
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge :
        CFSG.RankThree.PartOne.TauCetiCatalogBridge) _ hSnc hcat
    rcases hCat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hex | hsp
    · exfalso
      obtain ⟨a, b, hab⟩ := hSnc
      exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
    · exfalso
      exact CFSG.LocalAnalysis.UniquenessCase.UC22.false_of_unitary_alternating_quotient
        hXK hXq hQ hX hr hn e
    · obtain ⟨t, n, p, f, h⟩ := hcl
      have ht : t ∈ classicalTags := k329lie_tag_mem_classical _ t n p f h
      have hL : LieModel (↥K ⧸ Subgroup.center ↥K) t n p f := Or.inl ⟨ht, h⟩
      by_cases hp3 : p = 3
      · subst hp3
        exact absurd h19 (k329in_char3_classical_nineteen_free _ t n f ht hL hrS)
      · exact ⟨t, n, p, f, hL, hp3⟩
    · rcases hex with ⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩
      · have hL : LieModel (↥K ⧸ Subgroup.center ↥K) t 0 p f := Or.inr (Or.inl ⟨rfl, ht, h⟩)
        by_cases hp3 : p = 3
        · subst hp3
          exact absurd h19 (k329in_char3_exceptional_nineteen_free _ t 0 f
            (by cases t <;> simp_all [classicalTags, chevalleyExceptionalTags]) hL hrS)
        · exact ⟨t, 0, p, f, hL, hp3⟩
      · have hL : LieModel (↥K ⧸ Subgroup.center ↥K) t 0 p f :=
          Or.inr (Or.inr (Or.inl ⟨rfl, ht, h⟩))
        by_cases hp3 : p = 3
        · subst hp3
          exact absurd h19 (k329in_char3_exceptional_nineteen_free _ t 0 f
            (by cases t <;> simp_all [classicalTags, reeTitsTags]) hL hrS)
        · exact ⟨t, 0, p, f, hL, hp3⟩
      · have hL : LieModel (↥K ⧸ Subgroup.center ↥K) .twistedB2 0 p f :=
          Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))
        by_cases hp3 : p = 3
        · subst hp3
          exact absurd h19 (k329in_char3_exceptional_nineteen_free _ .twistedB2 0 f
            (by simp [classicalTags]) hL hrS)
        · exact ⟨.twistedB2, 0, p, f, hL, hp3⟩
    · exfalso
      obtain ⟨s, ⟨e0⟩⟩ := hsp
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
      exact CFSG.LocalAnalysis.UniquenessCase.UC22.false_of_unitary_sporadic_quotient
        hXK hXq hQ hX hr hZ (e0.trans b)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
