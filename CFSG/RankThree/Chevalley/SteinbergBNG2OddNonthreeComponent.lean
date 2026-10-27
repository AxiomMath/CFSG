module

public import CFSG.RankThree.Chevalley.SteinbergBNG2SplitInnerComponent
public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusInnerComponent
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.LieType.Chevalley.ExactG2FiniteOrder

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace SteinbergBN

theorem dvd_cyclotomic_factor_of_dvd_card_G2 {K : Type} [Field K] [Finite K] {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hpC : p ∣ Nat.card (adjointGroup .G2 K)) :
    p ∣ ℓ ^ f - 1 ∨ p ∣ ℓ ^ f + 1 ∨ p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1 ∨
      p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := by
  rw [(exact_G2_finite_order K hK).1] at hpC
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hpq : ¬ p ∣ ℓ ^ f := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  have hsq : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
    zify [hq1, Nat.one_le_pow 2 (ℓ ^ f) hq1]
    ring
  rcases (Nat.Prime.dvd_mul hp).1 hpC with h | h4
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h3
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h2
      · exact absurd (hp.dvd_of_dvd_pow h) hpq
      · have h2' := hp.dvd_of_dvd_pow h2
        rw [hsq] at h2'
        rcases (Nat.Prime.dvd_mul hp).1 h2' with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

end SteinbergBN

open SteinbergBN

theorem odd_nonthree_G2_cross_prime_actual_component_odd_action {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hℓp : ℓ ≠ p)
    (hf : 1 ≤ f) (hT : ChevalleyExceptionalModel (L ⧸ center L) .G2 ℓ f)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G)) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
        Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
        Set G) * (thetaT p E : Set G) ∧
    ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
      normalizer (L : Set G) ∧
    ¬ 2 ∣ (centralizer (L : Set G)).relIndex
      (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ∧
    (E ⊓ centralizer (L : Set G) ≠ ⊥ →
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G)) := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t ht ht1
  set W := ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E
    with hW
  have hcentral : W ≤ centralizer (L : Set G) →
      W ≤ normalizer (L : Set G) ∧ ¬ 2 ∣ (centralizer (L : Set G)).relIndex W := fun hWC =>
    ⟨hWC.trans (Subgroup.centralizer_le_normalizer (L : Set G)), by
      rw [Subgroup.relIndex_eq_one.mpr hWC]
      omega⟩
  have hnonfaith : E ⊓ centralizer (L : Set G) ≠ ⊥ → W ≤ centralizer (L : Set G) := fun hC =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Coprime.nonfaithful_plane_local_core_product_centralizes_component hp hE hEcard ht ht1 hL
        (commutator_le_normalizer_of_le hSL hEL) hC).2.2
  suffices h : W ≤ normalizer (L : Set G) ∧ ¬ 2 ∣ (centralizer (L : Set G)).relIndex W from
    ⟨hset, h.1, h.2, hnonfaith⟩
  by_cases hC : E ⊓ centralizer (L : Set G) = ⊥
  swap
  · exact hcentral (hnonfaith hC)
  by_cases hinn : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∈
      (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range
  swap
  · exact hcentral (odd_G2_noninner_cross_prime_actual_component_local_core_product_centralizes
      hp hp3 hE hEcard ht ht1 hL hℓ hℓ2 hℓ3 hf hT hEL hSL hinn).2
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hT.2
  obtain ⟨-, -, -, -, -, -, -, htbar, -⟩ :=
    SteinbergBM.faithful_component_local_core_almost_simple_image hp hp2 hE hEcard ht ht1 hL hEL
      hSL hC
  have hπt1 : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ≠ 1 := fun h => htbar (Subtype.ext h)
  have htp : t ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) t ht
  have hπtp : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ^ p = 1 := by
    rw [← map_pow]
    convert map_one (Finkelstein1977.automizer L)
    exact Subtype.ext htp
  have hZ : center (L ⧸ center L) = ⊥ := by
    rw [← Subgroup.map_center_eq e, center_adjointGroup_eq_bot, Subgroup.map_bot]
  have hinjT : Function.Injective
      (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)) :=
    mulAut_conj_injective_of_center_eq_bot hZ
  obtain ⟨x, hx⟩ := hinn
  have hx1 : x ≠ 1 := fun h => hπt1 (by rw [← hx, h, map_one])
  have hxp : orderOf x = p :=
    orderOf_eq_prime (hinjT (by rw [map_pow, hx, hπtp, map_one])) hx1
  have hpC : p ∣ Nat.card (adjointGroup .G2 K) := by
    rw [Nat.card_congr e.toEquiv, ← hxp]
    exact orderOf_dvd_natCard x
  have hinn : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∈
      (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range := ⟨x, hx⟩
  rcases dvd_cyclotomic_factor_of_dvd_card_G2 hℓ hK hp hℓp.symm hpC with h | h | h | h
  · exact ((odd_G2_split_cross_prime_inner_actor_actual_component_odd_action hp hp3 hE hEcard ht
      ht1 hL hℓ hℓ2 hℓ3 hf h hT hEL hSL).1 hinn).2
  · exact ((odd_G2_qplus_inner_actor_actual_component_odd_action hp hp3 hE hEcard ht ht1 hL hℓ
      hℓ2 hℓ3 hf h hT hEL hSL).1 hinn).2
  · have hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 * (ℓ ^ f : ℕ) + 1 := by
      have h' := Int.natCast_dvd_natCast.mpr h
      push_cast at h' ⊢
      simpa using h'
    exact ((odd_G2_cyclotomic_three_six_inner_actor_actual_component_odd_action hp hp3 hE hEcard
      ht ht1 hL hℓ hℓ2 hℓ3 hf 1 (Or.inr rfl) hpq hT hEL hSL).1 hinn).2
  · have hle : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * (ℓ ^ f : ℕ) + 1 := by
      have h' := Int.natCast_dvd_natCast.mpr h
      rw [Nat.cast_add, Nat.cast_sub hle] at h'
      push_cast at h' ⊢
      convert h' using 1
      ring
    exact ((odd_G2_cyclotomic_three_six_inner_actor_actual_component_odd_action hp hp3 hE hEcard
      ht ht1 hL hℓ hℓ2 hℓ3 hf (-1) (Or.inl rfl) hpq hT hEL hSL).1 hinn).2

end CFSG.RankThree.Chevalley
