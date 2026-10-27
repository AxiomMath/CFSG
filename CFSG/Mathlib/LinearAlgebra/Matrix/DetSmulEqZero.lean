module

public import Mathlib.LinearAlgebra.Matrix.Adjugate

public section

namespace CFSG.MatrixDet

theorem smul_det_eq_zero_of_sum_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [AddCommGroup G] (A : Matrix ι ι ℤ) (x : ι → G)
    (h : ∀ k, ∑ l, A k l • x l = 0) (j : ι) : A.det • x j = 0 := by
  have e : A.det • x j = ∑ l, (A.adjugate * A) j l • x l := by
    rw [Matrix.adjugate_mul]
    simp [Matrix.smul_apply, Matrix.one_apply, ite_smul]
  rw [e]
  simp_rw [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, h, smul_zero, Finset.sum_const_zero]

theorem pow_det_eq_one_of_prod_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [CommGroup G] (A : Matrix ι ι ℤ) (b : ι → G)
    (h : ∀ k, ∏ l, b l ^ A k l = 1) (j : ι) : b j ^ A.det = 1 := by
  have h' := smul_det_eq_zero_of_sum_eq_zero A (fun l => Additive.ofMul (b l))
    (fun k => by
      have hk := congrArg Additive.ofMul (h k)
      simpa [ofMul_prod, ofMul_zpow] using hk) j
  refine Additive.ofMul.injective (a₁ := b j ^ A.det) (a₂ := 1) ?_
  rw [ofMul_zpow]
  exact h'

end CFSG.MatrixDet

end
