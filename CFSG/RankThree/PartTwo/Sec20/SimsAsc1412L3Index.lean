module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAsc1411
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Hyp
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Models.PGLSimple
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.GH74.Filter.Small.RankThree
import CFSG.LargeExtraspecial.OutSixBasic
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Open (StatedProj StatedSL StatedSU)

@[expose] def IsL3eps1412 (G : Type) [Group G] (p : ℕ) [Fact p.Prime] : Prop :=
  3 < p ∧ ((p % 3 = 2 ∧ Nonempty (G ≃* projSL 3 (GaloisField p 1))) ∨
    (p % 3 = 1 ∧ Nonempty (G ≃* projSU 3 p 1)))

section Models

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

private theorem statedLieAdmissible_psl_three :
    CFSG.Open.StatedLieAdmissible .PSL 3 p 1 :=
  ⟨Fact.out, le_rfl, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
    fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩

private theorem statedLieAdmissible_psu_three (hp : 3 < p) :
    CFSG.Open.StatedLieAdmissible .PSU 3 p 1 :=
  ⟨Fact.out, le_rfl, le_rfl, fun h => by
    have h2 := (Prod.mk.inj h).2
    rw [pow_one] at h2
    omega⟩

private theorem statedClassicalModel_of_isL3eps1412 (h : IsL3eps1412 G p) :
    (p % 3 = 2 ∧ CFSG.Open.StatedClassicalModel G .PSL 3 p 1) ∨
      (p % 3 = 1 ∧ CFSG.Open.StatedClassicalModel G .PSU 3 p 1) := by
  obtain ⟨hp3, ⟨hp, ⟨e⟩⟩ | ⟨hp, ⟨e⟩⟩⟩ := h
  · exact Or.inl ⟨hp, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL
      statedLieAdmissible_psl_three e⟩
  · exact Or.inr ⟨hp, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      (statedLieAdmissible_psu_three hp3) e⟩

private theorem finite_of_isL3eps1412 (h : IsL3eps1412 G p) : Finite G := by
  rcases statedClassicalModel_of_isL3eps1412 h with ⟨-, -, K, _, _, -, ⟨e⟩⟩ |
    ⟨-, -, K, _, _, -, ⟨e⟩⟩
  · exact Finite.of_equiv _ e.symm.toEquiv
  · exact Finite.of_equiv _ e.symm.toEquiv

theorem isSimpleGroup_of_isL3eps1412 (h : IsL3eps1412 G p) : IsSimpleGroup G := by
  obtain ⟨hp3, ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩⟩ := h
  · have := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p 1)
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact e.isSimpleGroup
  · have := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible (statedLieAdmissible_psu_three hp3)
    exact e.isSimpleGroup

private theorem isPerfect_of_mulEquiv {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (e : A ≃* B) : Group.IsPerfect B :=
  Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

private theorem isPerfect_of_isL3eps1412 (h : IsL3eps1412 G p) : Group.IsPerfect G := by
  rcases statedClassicalModel_of_isL3eps1412 h with ⟨-, -, K, _, _, -, ⟨e⟩⟩ |
    ⟨-, hadm, K, _, _, hK, ⟨e⟩⟩
  · have := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 3) (by norm_num)
      (Or.inl le_rfl)
    exact isPerfect_of_mulEquiv
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).trans e.symm)
  · have := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (n := 3) le_rfl hadm.2.2.2
    have : Group.IsPerfect (StatedProj (StatedSU 3 (p ^ 1) K)) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    exact isPerfect_of_mulEquiv e.symm

theorem center_eq_bot_of_isL3eps1412 (h : IsL3eps1412 G p) : Subgroup.center G = ⊥ := by
  have := isSimpleGroup_of_isL3eps1412 h
  have := isPerfect_of_isL3eps1412 h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · exact hb
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top G).2 ht
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_ne_bot h1

theorem twoRank_le_two_of_isL3eps1412 [Finite G] (h : IsL3eps1412 G p) :
    CFSG.Open.twoRank G ≤ 2 := by
  have hp2 : p ≠ 2 := by have := h.1; omega
  rcases statedClassicalModel_of_isL3eps1412 h with ⟨-, hm⟩ | ⟨-, hm⟩
  · exact CFSG.GH74.Filter.t_PSL_three_odd G p 1 hp2 hm
  · exact CFSG.GH74.Filter.t_PSU_three_odd G p 1 hp2 hm

theorem card_outer_dvd_two_of_isL3eps1412 (h : IsL3eps1412 G p) : Nat.card (Outer G) ∣ 2 := by
  have := finite_of_isL3eps1412 h
  rcases statedClassicalModel_of_isL3eps1412 h with ⟨hp, hm⟩ | ⟨hp, hm⟩
  · have hd := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) (le_refl 3) Fact.out le_rfl hm).1
    have hg : Nat.gcd 3 (p ^ 1 - 1) = 1 := by
      rw [pow_one]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    have hdp : CFSG.RankThree.OuterOrder.determinantParameter .PSL 3 (p ^ 1) = 1 := hg
    rw [hdp] at hd
    simpa using hd
  · have hd := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) (le_refl 3) Fact.out le_rfl hm).1
    have hg : Nat.gcd 3 (p ^ 1 + 1) = 1 := by
      rw [pow_one]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    have hdp : CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (p ^ 1) = 1 := hg
    rw [hdp] at hd
    simpa using hd

end Models

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

theorem centralizer_map_eq_bot_of_hyp1411 (h : Hyp1411 X L S)
    (hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥) :
    Subgroup.centralizer ((L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) :
      Subgroup (X ⧸ CFSG.pPrimeCore 3 X)) : Set (X ⧸ CFSG.pPrimeCore 3 X)) = ⊥ := by
  set K := CFSG.pPrimeCore 3 X
  have hF : CFSG.generalizedFitting (X ⧸ K) = L.map (QuotientGroup.mk' K) := h.2.2.2.1
  refine eq_bot_iff.2 fun c hc => ?_
  have hcL : c ∈ L.map (QuotientGroup.mk' K) := by
    rw [← hF]
    refine CFSG.centralizer_generalizedFitting_le _ ?_
    rw [hF]
    exact hc
  have hzc : (⟨c, hcL⟩ : ↥(L.map (QuotientGroup.mk' K))) ∈
      center ↥(L.map (QuotientGroup.mk' K)) := by
    rw [mem_center_iff]
    rintro ⟨y, hy⟩
    exact Subtype.ext (mem_centralizer_iff.1 hc y hy)
  rw [hZ, mem_bot] at hzc
  exact mem_bot.2 (congrArg Subtype.val hzc)

theorem index_map_le_two_of_hyp1411 (h : Hyp1411 X L S)
    (hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥)
    (hout : Nat.card (Outer ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) ∣ 2) :
    (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).index ≤ 2 := by
  have : (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).Normal :=
    h.2.1.map _ (QuotientGroup.mk'_surjective _)
  have hC : centralizer ((L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) :
      Subgroup (X ⧸ CFSG.pPrimeCore 3 X)) : Set (X ⧸ CFSG.pPrimeCore 3 X)) ≤
        L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) :=
    (centralizer_map_eq_bot_of_hyp1411 h hZ).le.trans bot_le
  exact Nat.le_of_dvd two_pos
    ((CFSG.LargeExtraspecial.S14.index_dvd_card_outer _ hC).trans hout)

theorem relIndex_pCore_le_eight_of_hyp1411 (h : Hyp1411 X L S)
    (hrank : CFSG.Open.twoRank ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≤ 2)
    (hidx2 : (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).index ≤ 2) :
    ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 8 := by
  intro A hAS hA
  set K := CFSG.pPrimeCore 3 X
  set π := QuotientGroup.mk' K
  have hLn : (L.map π).Normal := h.2.1.map _ (QuotientGroup.mk'_surjective _)
  have hKA : K ⊓ A ≤ CFSG.pCore 2 X := fun x hx =>
    mem_pCore_of_mem_pPrimeCore_of_hyp1411 h (hAS hx.2) hx.1
  have h1 : (CFSG.pCore 2 X).relIndex A ∣ Nat.card (A.map π) := by
    rw [← relIndex_ker, QuotientGroup.ker_mk', ← inf_relIndex_right K A]
    exact relIndex_dvd_of_le_left A hKA
  have hB : Sec3.IsElemTwo (A.map π) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hA.1 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hA.2 a ha, map_one]
  have hinf : Nat.card ↥(L.map π ⊓ A.map π) ≤ 4 := by
    have h2 := Sec3.card_le_two_pow_pRank (T := L.map π) inf_le_left
      (A := L.map π ⊓ A.map π) ⟨fun a ha b hb => hB.1 a ha.2 b hb.2, fun a ha => hB.2 a ha.2⟩
    have h3 : CFSG.pRank 2 ↥(L.map π) ≤ 2 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hrank
    have h4 : 2 ^ CFSG.pRank 2 ↥(L.map π) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h3
    exact h2.trans (h4.trans (by norm_num))
  have hrel : (L.map π).relIndex (A.map π) ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_normal _ _)).trans hidx2
  have hcard : Nat.card (A.map π) ≤ 8 := by
    rw [← Subgroup.relIndex_mul_card (H := L.map π) (K := A.map π)]
    calc (L.map π).relIndex (A.map π) * Nat.card ↥(L.map π ⊓ A.map π) ≤ 2 * 4 :=
          Nat.mul_le_mul hrel hinf
      _ = 8 := by norm_num
  exact (Nat.le_of_dvd Nat.card_pos h1).trans hcard

theorem relIndex_pCore_le_eight_of_isL3eps1412 (h : Hyp1411 X L S) {p : ℕ} [Fact p.Prime]
    (hL : IsL3eps1412 ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) p) :
    ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 8 :=
  relIndex_pCore_le_eight_of_hyp1411 h (twoRank_le_two_of_isL3eps1412 hL)
    (index_map_le_two_of_hyp1411 h (center_eq_bot_of_isL3eps1412 hL)
      (card_outer_dvd_two_of_isL3eps1412 hL))

theorem index_map_le_two_of_isL3eps1412 (h : Hyp1411 X L S) {p : ℕ} [Fact p.Prime]
    (hL : IsL3eps1412 ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) p) :
    (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).index ≤ 2 :=
  index_map_le_two_of_hyp1411 h (center_eq_bot_of_isL3eps1412 hL)
    (card_outer_dvd_two_of_isL3eps1412 hL)

end CFSG.RankThree.PartTwo.Sec20
