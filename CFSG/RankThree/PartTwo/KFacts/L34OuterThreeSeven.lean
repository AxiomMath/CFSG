module

public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL coe_diagGL)
open Matrix

variable {k : Type*} [Field k]

theorem pow_seven_eq_one_of_cube {R : Type*} [Ring R] {z : R} (hzz : z + z = 0)
    (h : z ^ 3 = z + 1) : z ^ 7 = 1 := by
  have hsq : (z + 1) * (z + 1) = z * z + 1 := by
    calc (z + 1) * (z + 1) = z * z + (z + z) + 1 := by noncomm_ring
      _ = z * z + 1 := by rw [hzz, add_zero]
  calc z ^ 7 = z ^ 3 * z ^ 3 * z := by
        rw [show (7 : ℕ) = 3 + 3 + 1 from rfl, pow_succ z (3 + 3), pow_add z 3 3]
    _ = (z * z + 1) * z := by rw [h, hsq]
    _ = z ^ 3 + z := by rw [add_mul, one_mul, pow_three']
    _ = 1 := by
      have e : z + 1 + z = 1 + (z + z) := by abel
      rw [h, e, hzz, add_zero]

section Matrices

variable {a : k}

theorem add_self_matrix_eq_zero (h2 : (2 : k) = 0) {M : Matrix (Fin 3) (Fin 3) k} :
    M + M = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, ← two_mul, h2, zero_mul]

theorem det_zetaOne (h2 : (2 : k) = 0) (huu : a * a = a + 1) :
    (!![0, 1, a; 1, 0, 1; a * a, 1, 0] : Matrix (Fin 3) (Fin 3) k).det = 1 := by
  simp [Matrix.det_fin_three]
  grind

theorem cube_zetaOne (h2 : (2 : k) = 0) (huu : a * a = a + 1) (ha3 : a ^ 3 = 1) :
    (!![0, 1, a; 1, 0, 1; a * a, 1, 0] : Matrix (Fin 3) (Fin 3) k) ^ 3 =
      !![0, 1, a; 1, 0, 1; a * a, 1, 0] + 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [pow_succ, Matrix.mul_fin_three, Matrix.one_apply]
  all_goals grind

theorem comm_zetaOne (ha3 : a ^ 3 = 1) :
    (!![0, 0, a; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) k) *
        !![0, 1, a; 1, 0, 1; a * a, 1, 0] =
      !![0, 1, a; 1, 0, 1; a * a, 1, 0] * !![0, 0, a; 1, 0, 0; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_fin_three]
  all_goals grind

theorem det_zetaTwo (h2 : (2 : k) = 0) (huu : a * a = a + 1) :
    (!![0, a, 1; a * a, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) k).det = 1 := by
  simp [Matrix.det_fin_three]
  grind

theorem cube_zetaTwo (h2 : (2 : k) = 0) (huu : a * a = a + 1) (ha3 : a ^ 3 = 1) :
    (!![0, a, 1; a * a, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) k) ^ 3 =
      !![0, a, 1; a * a, 0, 1; 1, 1, 0] + 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [pow_succ, Matrix.mul_fin_three, Matrix.one_apply]
  all_goals grind

theorem comm_zetaTwo (ha3 : a ^ 3 = 1) :
    (!![0, a, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) k) *
        !![0, a, 1; a * a, 0, 1; 1, 1, 0] =
      !![0, a, 1; a * a, 0, 1; 1, 1, 0] * !![0, a, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_fin_three]
  all_goals grind

end Matrices

theorem orderOf_proj_eq_seven {z : Matrix.SpecialLinearGroup (Fin 3) k}
    (hzz : (z : Matrix (Fin 3) (Fin 3) k) + (z : Matrix (Fin 3) (Fin 3) k) = 0)
    (h3 : (z : Matrix (Fin 3) (Fin 3) k) ^ 3 = (z : Matrix (Fin 3) (Fin 3) k) + 1)
    (h01 : (z : Matrix (Fin 3) (Fin 3) k) 0 1 ≠ 0) : orderOf (proj 3 k z) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpow : z ^ 7 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_seven_eq_one_of_cube hzz h3,
      Matrix.SpecialLinearGroup.coe_one]
  apply orderOf_eq_prime
  · rw [← map_pow, hpow, map_one]
  · intro h
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
    have h' := congrFun (congrFun hc 0) 1
    simp [scalar_apply] at h'
    exact h01 h'

theorem coe_diagGL_mul_toGL_rSL (u : kˣ) :
    ((diagGL u * Matrix.SpecialLinearGroup.toGL rSL : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) = !![0, 0, (u : k); 1, 0, 0; 0, 1, 0] := by
  ext i j
  rw [Units.val_mul, coe_diagGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_rSL']
  fin_cases i <;> fin_cases j <;> simp [rM, Matrix.mul_fin_three]

theorem coe_diagGL_mul_toGL_rSL_sq (u : kˣ) :
    ((diagGL u * Matrix.SpecialLinearGroup.toGL rSL ^ 2 : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) = !![0, (u : k), 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  rw [Units.val_mul, coe_diagGL, Units.val_pow_eq_pow_val,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_rSL', pow_two]
  fin_cases i <;> fin_cases j <;> simp [rM, Matrix.mul_fin_three]

theorem xDiag_mul_yInn_eq_conjAut (u : kˣ) :
    xDiag u * yInn = conjAut 3 k (diagGL u * Matrix.SpecialLinearGroup.toGL rSL) := by
  rw [xDiag, yInn, bP, ← conjAut_toGL, map_mul]

theorem xDiag_mul_yInn_sq_eq_conjAut (u : kˣ) :
    xDiag u * yInn ^ 2 = conjAut 3 k (diagGL u * Matrix.SpecialLinearGroup.toGL rSL ^ 2) := by
  rw [xDiag, yInn, bP, ← conjAut_toGL, map_mul, map_pow]

theorem conjAut_proj_fix_of_comm {g : GL (Fin 3) k} {z : Matrix.SpecialLinearGroup (Fin 3) k}
    (hc : (g : Matrix (Fin 3) (Fin 3) k) * (z : Matrix (Fin 3) (Fin 3) k) =
      (z : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k)) :
    conjAut 3 k g (proj 3 k z) = proj 3 k z := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, hc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    mul_one]

theorem exists_orderOf_seven_fixed_xDiag_mul_yInn (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    ∃ y : projectiveSL 3 k, orderOf y = 7 ∧ (xDiag u * yInn : MulAut (projectiveSL 3 k)) y = y := by
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have huu : (u : k) * u = u + 1 := LinearFieldFour.omega_mul_omega hk u.ne_zero (val_ne_one hu)
  have ha3 : (u : k) ^ 3 = 1 := LinearFieldFour.pow_three_eq_one hk u.ne_zero
  refine ⟨proj 3 k ⟨!![0, 1, (u : k); 1, 0, 1; (u : k) * u, 1, 0], det_zetaOne h2 huu⟩,
    ?_, ?_⟩
  · apply orderOf_proj_eq_seven
    · exact add_self_matrix_eq_zero h2
    · exact cube_zetaOne h2 huu ha3
    · simp
  · rw [xDiag_mul_yInn_eq_conjAut]
    apply conjAut_proj_fix_of_comm
    rw [coe_diagGL_mul_toGL_rSL]
    exact comm_zetaOne ha3

theorem exists_orderOf_seven_fixed_xDiag_mul_yInn_sq (hk : Nat.card k = 4) {u : kˣ}
    (hu : u ≠ 1) :
    ∃ y : projectiveSL 3 k, orderOf y = 7 ∧
      (xDiag u * yInn ^ 2 : MulAut (projectiveSL 3 k)) y = y := by
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have huu : (u : k) * u = u + 1 := LinearFieldFour.omega_mul_omega hk u.ne_zero (val_ne_one hu)
  have ha3 : (u : k) ^ 3 = 1 := LinearFieldFour.pow_three_eq_one hk u.ne_zero
  refine ⟨proj 3 k ⟨!![0, (u : k), 1; (u : k) * u, 0, 1; 1, 1, 0], det_zetaTwo h2 huu⟩,
    ?_, ?_⟩
  · apply orderOf_proj_eq_seven
    · exact add_self_matrix_eq_zero h2
    · exact cube_zetaTwo h2 huu ha3
    · simpa using u.ne_zero
  · rw [xDiag_mul_yInn_sq_eq_conjAut]
    apply conjAut_proj_fix_of_comm
    rw [coe_diagGL_mul_toGL_rSL_sq]
    exact comm_zetaTwo ha3

end CFSG.RankThree.PartTwo.KFacts.L34
