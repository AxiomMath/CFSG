module

public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Open.StatedAPI
import CFSG.Assembly.E6FourLabelArith

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open

theorem ggF4H4Psl64_four_dvd {f : ℕ} (h : 5 ∣ 2 ^ f - 1) : 4 ∣ f :=
  CFSG.Assembly.e6Four_five_dvd_two_pow_sub_one.1 h

theorem ggF4H4Psl64_gcd_three {f : ℕ} (hf : 4 ∣ f) : Nat.gcd 3 (2 ^ f - 1) = 3 := by
  apply Nat.gcd_eq_left
  have h : 2 ^ 4 - 1 ∣ 2 ^ f - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hf
  exact (by norm_num : 3 ∣ 2 ^ 4 - 1).trans h

theorem ggF4H4Psl64_card_dvd {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 4 ∣ f) (hf2 : 2 ≤ f) :
    5 ∣ Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 3) F)) ∧
      13 ∣ Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 3) F)) ∧
      17 ∣ Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 3) F)) := by
  obtain ⟨k, rfl⟩ := hf
  set H : Subgroup (GL (Fin 3) F) := LargeEvenSLGroup (Fin 3) F with hH
  let q : ℕ := 2 ^ (4 * k)
  have hq : q = 2 ^ (4 * k) := rfl
  have hcardH : Nat.card H = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    rw [hH, largeEvenSLGroup_eq_statedSL (K := F) 3, StatedAPI.card_statedSL_three, hF]
  have hNcard : Nat.card H = Nat.card (LargeEvenProj H) *
      Nat.card ((LargeEvenScalars (Fin 3) F).subgroupOf H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hq2 : q ^ 2 - 1 = 2 ^ (8 * k) - 1 := by
    rw [hq, ← pow_mul, show (4 * k) * 2 = 8 * k by ring]
  have hq3 : q ^ 3 - 1 = 2 ^ (12 * k) - 1 := by
    rw [hq, ← pow_mul, show (4 * k) * 3 = 12 * k by ring]
  have d5 : 5 ∣ q ^ 2 - 1 := by
    rw [hq2]
    exact (by norm_num : 5 ∣ 2 ^ 4 - 1).trans
      (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (m := 4) (k := 8 * k)
        ⟨2 * k, by ring⟩)
  have d17 : 17 ∣ q ^ 2 - 1 := by
    rw [hq2]
    exact (by norm_num : 17 ∣ 2 ^ 8 - 1).trans
      (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (m := 8) (k := 8 * k) ⟨k, by ring⟩)
  have d13 : 13 ∣ q ^ 3 - 1 := by
    rw [hq3]
    exact (by norm_num : 13 ∣ 2 ^ 12 - 1).trans
      (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (m := 12) (k := 12 * k) ⟨k, by ring⟩)
  have h5card : 5 ∣ Nat.card H := by
    rw [hcardH]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left d5 (q ^ 3 - 1)) (q ^ 3)
  have h17card : 17 ∣ Nat.card H := by
    rw [hcardH]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left d17 (q ^ 3 - 1)) (q ^ 3)
  have h13card : 13 ∣ Nat.card H := by
    rw [hcardH]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d13 (q ^ 2 - 1)) (q ^ 3)
  have hd3 : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H → c ^ 3 = 1 := by
    intro c hc
    have hcSL : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedSL 3 F := by
      rw [← largeEvenSLGroup_eq_statedSL (K := F) 3]
      exact hc
    have hdet := StatedAPI.det_of_mem_statedSL hcSL
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by simpa using hdet)
  have hn5 : ¬ 5 ∣ Nat.card ((LargeEvenScalars (Fin 3) F).subgroupOf H) :=
    StatedAPI.not_dvd_card_statedScalars_subgroupOf H (by norm_num) (by norm_num) hd3
  have hn13 : ¬ 13 ∣ Nat.card ((LargeEvenScalars (Fin 3) F).subgroupOf H) :=
    StatedAPI.not_dvd_card_statedScalars_subgroupOf H (by norm_num) (by norm_num) hd3
  have hn17 : ¬ 17 ∣ Nat.card ((LargeEvenScalars (Fin 3) F).subgroupOf H) :=
    StatedAPI.not_dvd_card_statedScalars_subgroupOf H (by norm_num) (by norm_num) hd3
  have h5proj : 5 ∣ Nat.card (LargeEvenProj H) := by
    have h := h5card
    rw [hNcard] at h
    rcases (show Nat.Prime 5 by norm_num).dvd_mul.mp h with h | h
    · exact h
    · exact absurd h hn5
  have h13proj : 13 ∣ Nat.card (LargeEvenProj H) := by
    have h := h13card
    rw [hNcard] at h
    rcases (show Nat.Prime 13 by norm_num).dvd_mul.mp h with h | h
    · exact h
    · exact absurd h hn13
  have h17proj : 17 ∣ Nat.card (LargeEvenProj H) := by
    have h := h17card
    rw [hNcard] at h
    rcases (show Nat.Prime 17 by norm_num).dvd_mul.mp h with h | h
    · exact h
    · exact absurd h hn17
  exact ⟨h5proj, h13proj, h17proj⟩

end CFSG.StandardType
