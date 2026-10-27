module

public import Mathlib.Algebra.Group.Basic

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

theorem commute_of_sq_mul {a c : G} (ha : a * a = 1) (hc : c * c = 1) (hca : (c * a) ^ 2 = 1) :
    a * c = c * a := by
  have h1 : c * a * (c * a) = 1 := by rw [← pow_two]; exact hca
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have h2 : c * a = (c * a)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [mul_inv_rev, hai, hci] at h2
  exact h2.symm

theorem braid_of_cube {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) :
    a * b * a = b * a * b := by
  have h1 : a * b * a * (b * a * b) = 1 := by
    have : (a * b) ^ 3 = a * b * a * (b * a * b) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← this]; exact hab
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h2 : a * b * a = (b * a * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [h2, mul_inv_rev, mul_inv_rev, hai, hbi, mul_assoc]

theorem coxeter_A3_pow_four {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1) (hca : (c * a) ^ 2 = 1) :
    (a * b * c) ^ 4 = 1 := by
  have hac : a * c = c * a := commute_of_sq_mul ha hc hca
  have haba : a * b * a = b * a * b := braid_of_cube ha hb hab
  have hbcb : b * c * b = c * b * c := braid_of_cube hb hc hbc
  have hsq : (a * b * c) ^ 2 = b * a * c * b := by
    calc (a * b * c) ^ 2 = a * b * (c * a) * b * c := by
          simp only [pow_two, mul_assoc]
      _ = a * b * (a * c) * b * c := by rw [hac]
      _ = (a * b * a) * (c * b * c) := by simp only [mul_assoc]
      _ = (b * a * b) * (b * c * b) := by rw [haba, hbcb]
      _ = b * a * (b * b) * c * b := by simp only [mul_assoc]
      _ = b * a * c * b := by rw [hb, mul_one]
  have hcac : c * a * c = a := by
    rw [← hac, mul_assoc, hc, mul_one]
  calc (a * b * c) ^ 4 = (a * b * c) ^ 2 * (a * b * c) ^ 2 := by
        rw [← pow_add]
    _ = (b * a * c * b) * (b * a * c * b) := by rw [hsq]
    _ = b * a * c * (b * b) * a * c * b := by simp only [mul_assoc]
    _ = b * a * (c * a * c) * b := by rw [hb, mul_one]; simp only [mul_assoc]
    _ = b * (a * a) * b := by rw [hcac]; simp only [mul_assoc]
    _ = 1 := by rw [ha, mul_one, hb]

theorem coxeter_three_three_three_collapse {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1) (hca : (c * a) ^ 2 = 1)
    (habc : (a * b * c) ^ 3 = 1) : a = 1 ∧ b = 1 ∧ c = 1 := by
  have h4 := coxeter_A3_pow_four ha hb hc hab hbc hca
  have h1 : a * b * c = 1 := by
    have : (a * b * c) ^ 4 = (a * b * c) ^ 3 * (a * b * c) := pow_succ _ 3
    rw [this, habc, one_mul] at h4
    exact h4
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hc' : c = b * a := by
    have : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, mul_inv_rev, hai, hbi]
  have hab2 : a * b * (a * b) = 1 := by
    have h := hc
    rw [hc'] at h
    calc a * b * (a * b) = a * (b * a * (b * a)) * a⁻¹ := by
          rw [hai]; simp only [mul_assoc, ha, mul_one]
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  have hab1 : a * b = 1 := by
    have : (a * b) ^ 3 = a * b * (a * b) * (a * b) := by
      simp only [pow_succ, pow_zero, one_mul]
    rw [this, hab2, one_mul] at hab
    exact hab
  have hba : b = a := by
    have := eq_inv_of_mul_eq_one_right hab1
    rw [hai] at this
    exact this
  have hc1 : c = 1 := by rw [hc', hba, ha]
  have hb1 : b = 1 := by
    have h := hbc
    rw [hc1, mul_one] at h
    have : b ^ 3 = b * (b * b) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this, hb, mul_one] at h
    exact h
  exact ⟨by rw [← hba, hb1], hb1, hc1⟩

end CFSG.Monster.GMS
