module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClass

public section

namespace CFSG.StandardType

namespace OrthD4

open CFSG.StandardType.Triality CFSG.StandardType.D4Rank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem theta_theta (y : Om8 K) : theta (theta y) = (theta : MulAut (Om8 K))⁻¹ y := by
  rw [← MulAut.mul_apply, ← sq, theta_sq]

theorem theta_inv_theta_inv (y : Om8 K) :
    (theta : MulAut (Om8 K))⁻¹ ((theta : MulAut (Om8 K))⁻¹ y) = theta y := by
  rw [← MulAut.mul_apply, ← sq, inv_pow, theta_sq, inv_inv]

theorem theta_zero_six {y : Om8 K} (hy : y ^ 3 = 1)
    (h : omFixDim y = 0 ∨ omFixDim y = 6) :
    (omFixDim (theta y) = 0 ∨ omFixDim (theta y) = 6) ∧
      (omFixDim ((theta : MulAut (Om8 K))⁻¹ y) = 0 ∨
        omFixDim ((theta : MulAut (Om8 K))⁻¹ y) = 6) := by
  have hcls := ggD4TrialityClassInput_holds K
  rcases h with h0 | h6
  · rcases (hcls y hy).2 h0 with h | h
    · refine ⟨Or.inr h, Or.inl ?_⟩
      have hz3 : (theta y) ^ 3 = 1 := by rw [← map_pow, hy, map_one]
      have h1 := ((hcls (theta y) hz3).1 h).1
      rwa [theta_theta] at h1
    · refine ⟨Or.inl ?_, Or.inr h⟩
      have hz3 : ((theta : MulAut (Om8 K))⁻¹ y) ^ 3 = 1 := by rw [← map_pow, hy, map_one]
      have h1 := ((hcls _ hz3).1 h).2
      rwa [theta_inv_theta_inv] at h1
  · obtain ⟨h1, h2⟩ := (hcls y hy).1 h6
    exact ⟨Or.inl h1, Or.inl h2⟩

theorem theta_pow_zero_six_iff {y : Om8 K} (hy : y ^ 3 = 1) (k : ℕ) :
    (omFixDim (((theta : MulAut (Om8 K)) ^ k) y) = 0 ∨
        omFixDim (((theta : MulAut (Om8 K)) ^ k) y) = 6) ↔
      (omFixDim y = 0 ∨ omFixDim y = 6) := by
  induction k with
  | zero => rw [pow_zero, MulAut.one_apply]
  | succ k ih =>
    set z := ((theta : MulAut (Om8 K)) ^ k) y with hz
    have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, hy, map_one]
    rw [pow_succ', MulAut.mul_apply, ← hz, ← ih]
    constructor
    · intro h
      have h1 := (theta_zero_six (by rw [← map_pow, hz3, map_one]) h).2
      rwa [MulAut.inv_apply_self] at h1
    · intro h
      exact (theta_zero_six hz3 h).1

theorem aut_zero_six_iff (α : MulAut (Om8 K)) {x : Om8 K} (hx : x ^ 3 = 1) :
    (omFixDim (α x) = 0 ∨ omFixDim (α x) = 6) ↔ (omFixDim x = 0 ∨ omFixDim x = 6) := by
  obtain ⟨ι, hι, k, c, hc, rfl⟩ := exists_inner_mul_theta_pow_mul α
  obtain ⟨γ, rfl⟩ := hι
  have hcx : omFixDim (c x) = omFixDim x := by
    obtain ⟨σ, rfl | rfl⟩ := hc
    · exact omFixDim_fieldAutP σ x
    · rw [MulAut.mul_apply, omFixDim_plusRefl, omFixDim_fieldAutP]
  have hc3 : (c x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  rw [MulAut.mul_apply, MulAut.mul_apply, omFixDim_conj, theta_pow_zero_six_iff hc3, hcx]

end OrthD4

end CFSG.StandardType
