module

public import CFSG.RankThree.GF2n.Parrott.QA45ListGroups
public import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups
open CFSG.Sporadic.Schreier (tab tab_eq)

private theorem sylowFive_facts {G : Type*} [Group G] [Finite G] {b w : G}
    (hG : Nat.card G = 51840) (hb : orderOf b = 5) (hw : orderOf w = 2) (hbw : b * w = w * b)
    (hN : Nat.card (Subgroup.normalizer (Subgroup.zpowers b : Set G)) = 40)
    (hC : Nat.card (Subgroup.centralizer ({b} : Set G)) = 10) (B : Subgroup G)
    (hB : Nat.card B = 5) :
    Nat.card (Subgroup.normalizer (B : Set G)) = 40 ∧
      Nat.card (Subgroup.centralizer (B : Set G)) = 10 ∧
      ∃ w' : G, orderOf w' = 2 ∧ IsConj w' w ∧
        Subgroup.centralizer (B : Set G) = B ⊔ Subgroup.zpowers w' := by
  have hFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hB₀ : Nat.card (Subgroup.zpowers b) = 5 := by rw [Nat.card_zpowers, hb]
  have hindex : ∀ C : Subgroup G, Nat.card C = 5 → C.index = 10368 := by
    intro C hC
    have := Subgroup.card_mul_index C
    rw [hC, hG] at this
    omega
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.exists_conj_of_isPGroup 5 (B := B) (B₀ := Subgroup.zpowers b)
    (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hB))
    (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hB₀))
    (by rw [hindex B hB]; norm_num) (by rw [hindex _ hB₀]; norm_num)
  subst hg
  have hC₀ : Nat.card (Subgroup.centralizer (Subgroup.zpowers b : Set G)) = 10 := by
    rw [CFSG.GroupTheory.centralizer_zpowers_eq]
    exact hC
  have hCeq : Subgroup.centralizer (Subgroup.zpowers b : Set G) =
      Subgroup.zpowers b ⊔ Subgroup.zpowers w := by
    have hWle : Subgroup.zpowers b ⊔ Subgroup.zpowers w ≤
        Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
      refine sup_le (Subgroup.le_centralizer _) (Subgroup.zpowers_le.2 ?_)
      rw [CFSG.GroupTheory.centralizer_zpowers_eq]
      exact Subgroup.mem_centralizer_singleton_iff.2 hbw.symm
    have h10 : 10 ≤ Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers w) := by
      have h5 : 5 ∣ Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers w) := by
        rw [← hB₀]
        exact Subgroup.card_dvd_of_le le_sup_left
      have h2 : 2 ∣ Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers w) := by
        have : Nat.card (Subgroup.zpowers w) = 2 := by rw [Nat.card_zpowers, hw]
        rw [← this]
        exact Subgroup.card_dvd_of_le le_sup_right
      exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5 h2)
    exact (Subgroup.eq_of_le_of_card_ge hWle (by rw [hC₀]; exact h10)).symm
  refine ⟨by rw [CFSG.GroupTheory.card_normalizer_map_conj]; exact hN,
    by rw [CFSG.GroupTheory.card_centralizer_map_conj]; exact hC₀, MulAut.conj g w, ?_,
    (isConj_iff.2 ⟨g, (MulAut.conj_apply g w).symm⟩).symm, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hw
  · rw [CFSG.GroupTheory.centralizer_map_conj, hCeq, Subgroup.map_sup]
    simp only [MonoidHom.map_zpowers]
    rfl

private theorem b5NormalizerCount_eq :
    b5NormalizerCount () = ((elemsT QA45).filter fun c =>
      decide (c * b5 * c⁻¹ ∈ [1, b5, b5 * b5, b5 * b5 * b5, b5 * b5 * b5 * b5])).length := by
  simp [b5NormalizerCount, tab_eq, tabList_eq]

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem qa45_sylowFive :
    ∀ B : Subgroup A45, Nat.card B = 5 →
      Nat.card (Subgroup.normalizer (B : Set A45)) = 40 ∧
      Nat.card (Subgroup.centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        Subgroup.centralizer (B : Set A45) = B ⊔ Subgroup.zpowers w := by
  intro B hB
  have hFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hA : Nat.card A45 = 51840 := card_QA45
  have hb5A : b5 ∈ QA45.originalSubgroup :=
    (mem_iff_sift QA45 QA45_ok b5).2 qa45L1Facts.b5_mem_A
  obtain ⟨b, hb⟩ : ∃ b : A45, (b : Equiv.Perm (Fin 45)) = b5 := ⟨⟨b5, hb5A⟩, rfl⟩
  have hbeq : b = ⟨b5, hb5A⟩ := Subtype.ext hb
  have hbpow : b ^ 5 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hb]
    exact qa45L1Facts.b5_pow_five)
  have hbne : b ≠ 1 := fun h =>
    qa45L1Facts.b5_ne_one (by rw [← hb]; exact congrArg Subtype.val h)
  have hbord : orderOf b = 5 := orderOf_eq_prime hbpow hbne
  have hN₀ : Nat.card (Subgroup.normalizer (Subgroup.zpowers b : Set A45)) = 40 := by
    have h := card_filter QA45 QA45_ok
      (p := fun c : Equiv.Perm (Fin 45) =>
        c * b5 * c⁻¹ ∈ [1, b5, b5 * b5, b5 * b5 * b5, b5 * b5 * b5 * b5])
    rw [← qa45L1Facts.b5_normalizer, b5NormalizerCount_eq, ← h]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff,
      CFSG.GroupTheory.mem_zpowers_five_iff hbord]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    have hy : ∀ y : A45, (y = 1 ∨ y = b ∨ y = b * b ∨ y = b * b * b ∨ y = b * b * b * b) ↔
        ((y : Equiv.Perm (Fin 45)) = 1 ∨ (y : Equiv.Perm (Fin 45)) = b5 ∨
        (y : Equiv.Perm (Fin 45)) = b5 * b5 ∨ (y : Equiv.Perm (Fin 45)) = b5 * b5 * b5 ∨
        (y : Equiv.Perm (Fin 45)) = b5 * b5 * b5 * b5) := by
      intro y
      simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one, hb]
    have h2 := hy (c * b * c⁻¹)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hb] at h2
    exact h2
  have hC₀ : Nat.card (Subgroup.centralizer ({b} : Set A45)) = 10 := by
    rw [hbeq, card_centralizer_QA45_eq_filter b5 hb5A, ← commCount_eq]
    exact qa45L1Facts.b5_centralizer
  have huv2 : orderOf (uA * vA) = 2 := by
    have hsq : (uA * vA) * (uA * vA) = 1 := by
      refine Subtype.ext ?_
      change u * v * (u * v) = 1
      calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [u_commute_v]
        _ = (u * u) * (v * v) := by group
        _ = 1 := by rw [u_sq, v_sq, one_mul]
    refine orderOf_eq_prime (by rw [sq]; exact hsq) fun h => ?_
    have h1 : u * v = 1 := by simpa using congrArg Subtype.val h
    have h2 : v = u := by
      calc v = (u * u) * v := by rw [u_sq, one_mul]
        _ = u * (u * v) := by rw [mul_assoc]
        _ = u := by rw [h1, mul_one]
    exact v_not_mem_Q (h2 ▸ u_mem_Q)
  have hcomm : b * (uA * vA) = (uA * vA) * b := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, hb]
    exact qa45L1Facts.b5_commutes
  exact sylowFive_facts hA hbord huv2 hcomm hN₀ hC₀ B hB

end CFSG.RankThree.GF2n.Parrott
