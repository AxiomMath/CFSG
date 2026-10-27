module

public import CFSG.LinearAlgebra.SL2CoprimeOrder

public section

namespace CFSG.Quasithin.QA24

open scoped MatrixGroups

variable {F : Type*} [Field F]

theorem trace_eq_neg_one_of_order_three (a : SL(2, F)) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) :
    (a : Matrix (Fin 2) (Fin 2) F).trace = -1 := by
  set A : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F) with hA
  have hdet : A.det = 1 := a.2
  have hA3 : A * (A * A) = 1 := by
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) ha3
    simpa [pow_succ, hA, mul_assoc] using this
  have hsq := CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one A hdet
  set t : F := A.trace with ht
  have hcube : (t ^ 2 - 1) • A = (1 + t) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : t • (t • A - (1 : Matrix (Fin 2) (Fin 2) F)) - A = 1 := by
      have h2 := hA3
      rw [hsq, mul_sub, mul_smul_comm, mul_one, hsq] at h2
      exact h2
    ext i j
    have h3 := congrFun (congrFun h1 i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h3 ⊢
    linear_combination h3
  by_cases hk : t ^ 2 - 1 = 0
  · rw [hk, zero_smul] at hcube
    have h00 := congrFun (congrFun hcube 0) 0
    simp only [Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      mul_one] at h00
    linear_combination -h00
  · exfalso
    have hA' : A = ((1 + t) / (t ^ 2 - 1)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [div_eq_inv_mul, mul_smul, ← hcube, smul_smul, inv_mul_cancel₀ hk, one_smul]
    set l : F := (1 + t) / (t ^ 2 - 1) with hl
    have h1 : l ^ 2 = 1 := by
      have := hdet
      rw [hA', Matrix.det_smul, Matrix.det_one] at this
      simpa using this
    have h3 : l ^ 3 = 1 := by
      have := congrFun (congrFun hA3 0) 0
      rw [hA'] at this
      simpa [pow_succ, mul_assoc] using this
    have hl1 : l = 1 := by
      have h4 : l = l ^ 3 := by
        calc l = l * 1 := (mul_one l).symm
          _ = l * l ^ 2 := by rw [h1]
          _ = l ^ 3 := by ring
      rw [h4, h3]
    apply ha1
    apply Subtype.ext
    rw [← hA, hA', hl1, one_smul]
    rfl

theorem false_of_commuting_order_three (h3 : (3 : F) ≠ 0) (a b : SL(2, F)) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a) (hba : b ≠ a)
    (hba2 : b ≠ a ^ 2) : False := by
  have hta := trace_eq_neg_one_of_order_three a ha1 ha3
  have htb := trace_eq_neg_one_of_order_three b hb1 hb3
  have hainv : a⁻¹ = a ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ha3)
  have hne1 : a * b ≠ 1 := by
    intro h
    exact hba2 (by rw [← hainv]; exact (eq_inv_of_mul_eq_one_right h))
  have hne2 : a * b ^ 2 ≠ 1 := by
    intro h
    apply hba
    have h1 : b ^ 2 = a ^ 2 := by rw [← hainv]; exact eq_inv_of_mul_eq_one_right h
    have h2 : b = b ^ 4 := by rw [pow_succ b 3, hb3, one_mul]
    have h3' : a = a ^ 4 := by rw [pow_succ a 3, ha3, one_mul]
    rw [h2, h3', show b ^ 4 = (b ^ 2) ^ 2 from pow_mul b 2 2,
      show a ^ 4 = (a ^ 2) ^ 2 from pow_mul a 2 2, h1]
  have hc1 : (a * b) ^ 3 = 1 := by
    rw [(show Commute a b from hab).mul_pow, ha3, hb3, one_mul]
  have hc2 : (a * b ^ 2) ^ 3 = 1 := by
    rw [((show Commute a b from hab).pow_right 2).mul_pow, ha3, ← pow_mul,
      show 2 * 3 = 3 * 2 by rfl, pow_mul, hb3, one_pow, one_mul]
  have ht1 := trace_eq_neg_one_of_order_three _ hne1 hc1
  have ht2 := trace_eq_neg_one_of_order_three _ hne2 hc2
  set A : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F) with hA
  set B : Matrix (Fin 2) (Fin 2) F := (b : Matrix (Fin 2) (Fin 2) F) with hB
  have hBB : B * B = -B - 1 := by
    rw [CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one B b.2, htb, neg_smul, one_smul]
  have hprod : ((a * b ^ 2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = A * (B * B) := by
    simp [pow_two, hA, hB]
  have hprod1 : ((a * b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = A * B := by simp [hA, hB]
  rw [hprod, hBB] at ht2
  rw [hprod1] at ht1
  have : (A * (-B - 1)).trace = -(A * B).trace - A.trace := by
    rw [mul_sub, mul_neg, mul_one, Matrix.trace_sub, Matrix.trace_neg]
  rw [this, ht1, hta] at ht2
  apply h3
  linear_combination ht2

end CFSG.Quasithin.QA24
