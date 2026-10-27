module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSectionBasic
public import Mathlib.GroupTheory.PGroup

import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.ShultStronglyClosedTI.CentralSection

open Subgroup
open scoped Pointwise

namespace SingerSection

variable {P X : Type*} [Group P] [Group X] {Q T : Subgroup P} {φ : X →* MulAut P}

theorem inv_mul_mem_of_sq_eq_one (h : SingerSection Q T φ) {t₀ : P} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1) {g g' : P} (hg : g ^ 2 = 1) (hg' : g' ^ 2 = 1) (hgH : g ∉ Q ⊔ T)
    (hκ : h.κ t₀ g = h.κ t₀ g') : g⁻¹ * g' ∈ Q := by
  have hmem : g⁻¹ * g' ∈ Q ⊔ T := by
    rw [← h.κ_eq_one_iff ht₀ ht₀1, map_mul, map_inv, hκ, inv_mul_cancel]
  have := h.normal
  rw [← SetLike.mem_coe, normal_mul, Set.mem_mul] at hmem
  obtain ⟨z, hz, t, ht, hzt⟩ := hmem
  by_cases ht1 : t = 1
  · rw [← hzt, ht1, mul_one]
    exact hz
  · refine absurd ?_ hgH
    have hg'eq : g' = g * z * t := by rw [mul_assoc, hzt]; group
    have key := h.mul_sq (g * z) t
    rw [← hg'eq, hg', h.sq_mul_of_mem g hz, hg, h.sq_eq_one_of_mem t ht, mul_one, mul_one] at key
    have hcomm : g * z ∈ centralizer {t} := by
      rw [mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp key.symm)).symm
    rw [h.centralizer_eq t ht ht1] at hcomm
    have hgz : g = g * z * z⁻¹ := by group
    rw [hgz]
    exact mul_mem hcomm (mem_sup_left (inv_mem hz))

theorem card_sq_eq_one_le (h : SingerSection Q T φ) [Finite P] {t₀ : P} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1) :
    Nat.card {g : P // g ^ 2 = 1} ≤
      Nat.card Q * Nat.card T + Nat.card Q * (Nat.card Q - 1) := by
  classical
  have := Fintype.ofFinite P
  let S : Finset P := Finset.univ.filter fun g => g ^ 2 = 1
  let QF : Finset P := Finset.univ.filter (· ∈ Q)
  have hcardF : ∀ K : Subgroup P, (Finset.univ.filter (· ∈ K)).card = Nat.card K := fun K => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hS : Nat.card {g : P // g ^ 2 = 1} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (S.filter (· ∈ Q ⊔ T)).card ≤ Nat.card Q * Nat.card T := by
    refine le_trans ?_ h.card_sup_le
    rw [← hcardF]
    exact Finset.card_le_card fun g hg => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hg ⊢
      exact hg.2
  have h2 : (S.filter (· ∉ Q ⊔ T)).card ≤ Nat.card Q * (Nat.card Q - 1) := by
    have hQF : (QF.erase 1).card = Nat.card Q - 1 := by
      rw [Finset.card_erase_of_mem
        (by simp only [QF, Finset.mem_filter, Finset.mem_univ, true_and, one_mem]), hcardF]
    rw [← hQF]
    refine Finset.card_le_mul_card_image_of_maps_to (f := h.κ t₀) ?_ _ ?_
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hg
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, QF]
      exact ⟨fun h1 => hg.2 ((h.κ_eq_one_iff ht₀ ht₀1).mp h1), h.κ_mem t₀ g⟩
    · intro c _
      rcases Finset.eq_empty_or_nonempty
          ((S.filter (· ∉ Q ⊔ T)).filter fun g => h.κ t₀ g = c) with hE | ⟨g₀, hg₀⟩
      · rw [hE, Finset.card_empty]
        exact Nat.zero_le _
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hg₀
        rw [← hcardF Q]
        refine le_trans (Finset.card_le_card fun g hg => ?_)
          (Finset.card_image_le (s := QF) (f := (g₀ * ·)))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hg
        rw [Finset.mem_image]
        refine ⟨g₀⁻¹ * g, ?_, by group⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, QF]
        exact h.inv_mul_mem_of_sq_eq_one ht₀ ht₀1 hg₀.1.1 hg.1.1 hg₀.1.2 (hg₀.2.trans hg.2.symm)
  rw [hS, ← Finset.card_filter_add_card_filter_not (s := S) (fun g => g ∈ Q ⊔ T)]
  exact Nat.add_le_add h1 h2

theorem le_two_of_count {q s : ℕ} (hq : 2 ≤ q) (h : q + q ^ 2 * (s - 1) ≤ q * s + q * (q - 1)) :
    s ≤ 2 := by
  by_contra hlt
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hq
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ s by omega)
  rw [show 3 + c - 1 = c + 2 by omega, show 2 + a - 1 = a + 1 by omega] at h
  nlinarith [Nat.zero_le (a * c), Nat.zero_le (a * a * c), Nat.zero_le (a * a)]

theorem card_le_two (h : SingerSection Q T φ) [Finite P] {t₀ : P} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1) (hQ2 : 2 ≤ Nat.card Q)
    (hcount : Nat.card {g : P // g ^ 2 = 1} = Nat.card Q + Nat.card Q ^ 2 * (Nat.card T - 1)) :
    Nat.card T ≤ 2 :=
  le_two_of_count hQ2 (hcount ▸ h.card_sq_eq_one_le ht₀ ht₀1)

theorem card_eq (h : SingerSection Q T φ) [Finite P] (hP : IsPGroup 2 P) {e : ℕ}
    (hQ : Nat.card Q = 2 ^ e) (hT : Nat.card T = 2) {t₀ : P} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1)
    (hcount : Nat.card {g : P // g ^ 2 = 1} = Nat.card Q + Nat.card Q ^ 2 * (Nat.card T - 1)) :
    Nat.card P = 2 * Nat.card Q ^ 2 ∧ Nat.card (Q ⊔ T : Subgroup P) = 2 * Nat.card Q := by
  have hlow : Nat.card Q + Nat.card Q ^ 2 ≤ Nat.card P := by
    have := Finite.card_subtype_le fun g : P => g ^ 2 = 1
    rw [hcount, hT] at this
    simpa using this
  have hmul : Nat.card P = Nat.card (Q ⊔ T : Subgroup P) * Nat.card (h.κ t₀).range := by
    rw [← index_ker, ← h.ker_κ ht₀ ht₀1, card_mul_index]
  have hrange : Nat.card (h.κ t₀).range ≤ Nat.card Q := by
    refine card_le_of_le ?_
    rintro _ ⟨a, rfl⟩
    exact h.κ_mem t₀ a
  have hH : Nat.card (Q ⊔ T : Subgroup P) ≤ 2 * Nat.card Q := by
    have := h.card_sup_le
    rw [hT] at this
    linarith
  have hup : Nat.card P ≤ 2 * Nat.card Q ^ 2 := by
    rw [hmul, sq, ← mul_assoc]
    exact Nat.mul_le_mul hH hrange
  have hPcard : Nat.card P = 2 * Nat.card Q ^ 2 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
    have hq0 : 0 < Nat.card Q := Nat.card_pos
    have hq2 : Nat.card Q ^ 2 = 2 ^ (2 * e) := by rw [hQ, ← pow_mul, mul_comm]
    rw [hq2, hn] at hup hlow ⊢
    have h1 : 2 * e < n := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by omega)
    have h2 : n ≤ 2 * e + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by rw [pow_succ]; omega)
    rw [show n = 2 * e + 1 by omega, pow_succ, mul_comm]
  refine ⟨hPcard, ?_⟩
  have hq : 0 < Nat.card Q := Nat.card_pos
  by_contra hne
  have hlt : Nat.card (Q ⊔ T : Subgroup P) < 2 * Nat.card Q := lt_of_le_of_ne hH hne
  have : Nat.card (Q ⊔ T : Subgroup P) * Nat.card (h.κ t₀).range < 2 * Nat.card Q ^ 2 := by
    calc Nat.card (Q ⊔ T : Subgroup P) * Nat.card (h.κ t₀).range
        ≤ Nat.card (Q ⊔ T : Subgroup P) * Nat.card Q := Nat.mul_le_mul_left _ hrange
      _ < 2 * Nat.card Q * Nat.card Q := Nat.mul_lt_mul_of_pos_right hlt hq
      _ = 2 * Nat.card Q ^ 2 := by ring
  omega

end SingerSection

end CFSG.ShultStronglyClosedTI.CentralSection
