module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

private theorem sl23_exists_sq_mul_sq (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), g = a ^ 2 * b ^ 2 := by
  revert g
  decide

private lemma sylow_card_and_index_cases {n i : ℕ} (hn : n ≠ 1) (hmod : n % 3 = 1)
    (hni : n ∣ i) (hi8 : i ∣ 8) : n = 4 ∧ (i = 4 ∨ i = 8) := by
  have hi_pos : 0 < i := Nat.pos_of_dvd_of_pos hi8 (by norm_num)
  have hnle : n ≤ 8 :=
    le_trans (Nat.le_of_dvd hi_pos hni) (Nat.le_of_dvd (by norm_num) hi8)
  have hile : i ≤ 8 := Nat.le_of_dvd (by norm_num) hi8
  have key : ∀ n : Fin 9, ∀ i : Fin 9,
      (n : ℕ) ≠ 1 → (n : ℕ) % 3 = 1 → (n : ℕ) ∣ (i : ℕ) → (i : ℕ) ∣ 8 →
      (n : ℕ) = 4 ∧ ((i : ℕ) = 4 ∨ (i : ℕ) = 8) := by decide
  exact key ⟨n, by omega⟩ ⟨i, by omega⟩ hn hmod hni hi8

private lemma sl23_card_eq_twelve_or_twentyfour
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (S : Sylow 3 H) (hS : ¬ (S : Subgroup H).Normal)
    (hcardH : Nat.card H ∣ 24) : Nat.card H = 12 ∨ Nat.card H = 24 := by
  have hn_ne_one : Nat.card (Sylow 3 H) ≠ 1 := by
    intro h1
    have hsub : Subsingleton (Sylow 3 H) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact hS (by haveI := hsub; exact Sylow.normal_of_subsingleton S)
  have hmod : Nat.card (Sylow 3 H) % 3 = 1 := by
    have h := card_sylow_modEq_one 3 H
    rw [Nat.ModEq] at h
    simpa using h
  have hcardS_ne_one : Nat.card (S : Subgroup H) ≠ 1 := by
    intro h1
    have hbot : (S : Subgroup H) = ⊥ := Subgroup.eq_bot_of_card_eq (S : Subgroup H) h1
    exact hS (hbot ▸ Subgroup.normal_bot)
  have h24fac : Nat.factorization 24 3 = 1 := by
    rw [show (24 : ℕ) = 3 * 8 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 3 8),
      Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 8), add_zero]
  have hk_dvd : 3 ^ Nat.factorization (Nat.card H) 3 ∣ 24 := by
    rw [← Sylow.card_eq_multiplicity S]
    exact (Subgroup.card_subgroup_dvd_card (S : Subgroup H)).trans hcardH
  have hk_le : Nat.factorization (Nat.card H) 3 ≤ 1 := by
    have h := (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : 24 ≠ 0)).mp hk_dvd
    rwa [h24fac] at h
  have hk_ne : Nat.factorization (Nat.card H) 3 ≠ 0 := by
    intro h0
    exact hcardS_ne_one (by rw [Sylow.card_eq_multiplicity S, h0, pow_zero])
  have hcardS : Nat.card (S : Subgroup H) = 3 := by
    rw [Sylow.card_eq_multiplicity S]
    have h1 : Nat.factorization (Nat.card H) 3 = 1 := by omega
    rw [h1, pow_one]
  have h3i : 3 * (S : Subgroup H).index = Nat.card H := by
    have h := Subgroup.card_mul_index (S : Subgroup H)
    rwa [hcardS] at h
  have hi8 : (S : Subgroup H).index ∣ 8 := by
    obtain ⟨c, hc⟩ := hcardH
    refine ⟨c, ?_⟩
    have h : 3 * 8 = 3 * ((S : Subgroup H).index * c) := by
      calc 3 * 8 = (24 : ℕ) := by norm_num
        _ = Nat.card H * c := hc
        _ = (3 * (S : Subgroup H).index) * c := by rw [← h3i]
        _ = 3 * ((S : Subgroup H).index * c) := by ring
    exact Nat.mul_left_cancel (by norm_num : 0 < 3) h
  obtain ⟨_, hi | hi⟩ :=
    sylow_card_and_index_cases hn_ne_one hmod (Sylow.card_dvd_index S) hi8
  · left; omega
  · right; omega

theorem sl23_eq_top_of_not_normal_sylow
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hH : ∃ S : Sylow 3 H, ¬ (S : Subgroup H).Normal) : H = ⊤ := by
  obtain ⟨S, hS⟩ := hH
  have hcardG : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hcardH : Nat.card H ∣ 24 := hcardG ▸ Subgroup.card_subgroup_dvd_card H
  rcases sl23_card_eq_twelve_or_twentyfour H S hS hcardH with h12 | h24
  · refine le_antisymm le_top ?_
    intro g _
    have hindex : H.index = 2 := by
      rw [Subgroup.index_eq_card_div (G := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)),
        hcardG, h12]
    obtain ⟨a, b, rfl⟩ := sl23_exists_sq_mul_sq g
    exact H.mul_mem (Subgroup.sq_mem_of_index_two hindex a)
      (Subgroup.sq_mem_of_index_two hindex b)
  · exact Subgroup.eq_top_of_card_eq H (h24.trans hcardG.symm)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
