module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

public section

namespace CFSG.Quasithin.L139A5

open Matrix

variable {K : Type*} [Field K]

theorem sq_eq_two (A : Matrix (Fin 2) (Fin 2) K) :
    A ^ 2 = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;>
    ring

theorem pow_five_eq (A : Matrix (Fin 2) (Fin 2) K) :
    A ^ 5 = (A.trace ^ 4 - 3 * A.trace ^ 2 * A.det + A.det ^ 2) • A -
      (A.trace ^ 3 * A.det - 2 * A.trace * A.det ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h2 := sq_eq_two A
  have h5 : A ^ 5 = A ^ 2 * A ^ 2 * A := by
    rw [← pow_add, ← pow_succ]
  rw [h5, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.sub_apply, Matrix.smul_apply] <;>
    ring

theorem trace_sq (A : Matrix (Fin 2) (Fin 2) K) :
    (A ^ 2).trace = A.trace ^ 2 - 2 * A.det := by
  rw [sq_eq_two A, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

theorem five_eq_zero_of_pow_five {A : Matrix (Fin 2) (Fin 2) K} {μ : K}
    (h5 : A ^ 5 = μ • (1 : Matrix (Fin 2) (Fin 2) K))
    (hns : ∀ r : K, A ≠ r • (1 : Matrix (Fin 2) (Fin 2) K)) :
    A.trace ^ 4 - 3 * A.trace ^ 2 * A.det + A.det ^ 2 = 0 := by
  by_contra hne
  apply hns ((μ + (A.trace ^ 3 * A.det - 2 * A.trace * A.det ^ 2)) /
    (A.trace ^ 4 - 3 * A.trace ^ 2 * A.det + A.det ^ 2))
  have h := pow_five_eq A
  rw [h5] at h
  have h' : (A.trace ^ 4 - 3 * A.trace ^ 2 * A.det + A.det ^ 2) • A =
      (μ + (A.trace ^ 3 * A.det - 2 * A.trace * A.det ^ 2)) •
        (1 : Matrix (Fin 2) (Fin 2) K) := by
    have e := add_smul μ (A.trace ^ 3 * A.det - 2 * A.trace * A.det ^ 2)
      (1 : Matrix (Fin 2) (Fin 2) K)
    rw [e, h, sub_add_cancel]
  rw [div_eq_inv_mul, mul_smul, ← h', smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem five_eq_zero_of_eqs {x δ : K} (hδ : δ ≠ 0)
    (h1 : x ^ 2 - 3 * x * δ + δ ^ 2 = 0) (h3 : δ * x = (x - 2 * δ) ^ 2) : (5 : K) = 0 := by
  have e : δ * (3 * δ - 2 * x) = 0 := by linear_combination (-1) * h1 + (-1) * h3
  have hx : 3 * δ - 2 * x = 0 := (mul_eq_zero.mp e).resolve_left hδ
  have h5 : 5 * δ ^ 2 = 0 := by linear_combination (-4) * h1 + (3 * δ - 2 * x) * hx
  exact (mul_eq_zero.mp h5).resolve_right (pow_ne_zero 2 hδ)

theorem false_of_conj_eq_sq (h5 : (5 : K) ≠ 0)
    {u h : ProjGenLinGroup (Fin 2) K} (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1)
    (hc : h * u * h⁻¹ = u ^ 2) : False := by
  obtain ⟨U, rfl⟩ := ProjGenLinGroup.mk_surjective u
  obtain ⟨H, rfl⟩ := ProjGenLinGroup.mk_surjective h
  set A : Matrix (Fin 2) (Fin 2) K := (U : Matrix (Fin 2) (Fin 2) K) with hA
  set B : Matrix (Fin 2) (Fin 2) K := (H : Matrix (Fin 2) (Fin 2) K) with hB
  obtain ⟨μ, hμ⟩ : ∃ μ : K, A ^ 5 = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← map_pow, ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hu5
    obtain ⟨r, hr⟩ := hu5
    refine ⟨r, ?_⟩
    rw [hA, ← Units.val_pow_eq_pow_val, ← hr, Matrix.smul_one_eq_diagonal]
    rfl
  have hns : ∀ r : K, A ≠ r • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro r hr
    apply hu1
    rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    exact ⟨r, by rw [← hA, hr, Matrix.smul_one_eq_diagonal]; rfl⟩
  have hU5 := five_eq_zero_of_pow_five hμ hns
  rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, ProjGenLinGroup.mk_eq_mk_iff] at hc
  obtain ⟨c, hc⟩ := hc
  have hcm : B * A * (↑(H⁻¹) : Matrix (Fin 2) (Fin 2) K) * ((c : K) • 1) = A ^ 2 := by
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hc
    simpa [Matrix.GeneralLinearGroup.coe_mul, Units.val_pow_eq_pow_val, Matrix.smul_one_eq_diagonal]
      using this
  have hHH : B * (↑(H⁻¹) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [hB, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hHH' : (↑(H⁻¹) : Matrix (Fin 2) (Fin 2) K) * B = 1 := by
    rw [hB, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hconj : (c : K) • (B * A * (↑(H⁻¹) : Matrix (Fin 2) (Fin 2) K)) = A ^ 2 := by
    rw [← hcm, Matrix.mul_smul, Matrix.mul_one]
  have htr : (c : K) * A.trace = A.trace ^ 2 - 2 * A.det := by
    have h1 := congrArg Matrix.trace hconj
    rw [Matrix.trace_smul, smul_eq_mul, trace_sq, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, hHH', Matrix.mul_one] at h1
    exact h1
  have hdetA : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp U.isUnit).ne_zero
  have hdet : (c : K) ^ 2 * A.det = A.det ^ 2 := by
    have h1 := congrArg Matrix.det hconj
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul, det_pow] at h1
    have hBi : B.det * (↑(H⁻¹) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [← Matrix.det_mul, hHH, Matrix.det_one]
    calc (c : K) ^ 2 * A.det =
          (c : K) ^ 2 * (B.det * A.det * (↑(H⁻¹) : Matrix (Fin 2) (Fin 2) K).det) := by
          rw [mul_comm B.det A.det, mul_assoc, hBi, mul_one]
      _ = A.det ^ 2 := h1
  have hc2 : (c : K) ^ 2 = A.det := by
    have := hdet
    rw [sq A.det] at this
    exact mul_right_cancel₀ hdetA this
  have hsq : A.det * A.trace ^ 2 = (A.trace ^ 2 - 2 * A.det) ^ 2 := by
    rw [← htr, mul_pow, hc2]
  exact h5 (five_eq_zero_of_eqs hdetA (by linear_combination hU5) hsq)

end CFSG.Quasithin.L139A5
