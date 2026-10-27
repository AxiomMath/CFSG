module

public import CFSG.RankThree.PartOne.KE.SLnFamily

public section

namespace CFSG.RankThree.Classical2

open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem conjSLn_one (A : SL(n, K)) : conjSLn (1 : GL (Fin n) K) A = A := by
  apply Subtype.ext
  rw [coe_conjSLn]
  simp

theorem conjSLn_mul (M N : GL (Fin n) K) (A : SL(n, K)) :
    conjSLn (M * N) A = conjSLn M (conjSLn N A) := by
  apply Subtype.ext
  rw [coe_conjSLn, coe_conjSLn, coe_conjSLn]
  simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem conjSLn_toGL (B A : SL(n, K)) :
    conjSLn (Matrix.SpecialLinearGroup.toGL B) A = B * A * B⁻¹ := by
  apply Subtype.ext
  rw [coe_conjSLn]
  have h : (((Matrix.SpecialLinearGroup.toGL B)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) := by
    rw [← map_inv]
    rfl
  rw [h]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rfl

theorem conjSLn_scalar (u : Kˣ) (A : SL(n, K)) :
    conjSLn (Matrix.GeneralLinearGroup.scalar (Fin n) u) A = A := by
  apply Subtype.ext
  rw [coe_conjSLn, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar]
  have hc : Matrix.scalar (Fin n) (u : K) * (A : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * Matrix.scalar (Fin n) (u : K) :=
    (Matrix.scalar_commute (u : K) (fun _ => mul_comm _ _) _).eq
  rw [hc, Matrix.mul_assoc, ← map_mul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ u.ne_zero,
    map_one, Matrix.mul_one]

theorem conjSLn_mul_scalar (M : GL (Fin n) K) (u : Kˣ) (A : SL(n, K)) :
    conjSLn (M * Matrix.GeneralLinearGroup.scalar (Fin n) u) A = conjSLn M A := by
  rw [conjSLn_mul, conjSLn_scalar]

theorem map_conjSLn (σ : K →+* K) (M : GL (Fin n) K) (A : SL(n, K)) :
    Matrix.SpecialLinearGroup.map σ (conjSLn M A) =
      conjSLn (Matrix.GeneralLinearGroup.map σ M) (Matrix.SpecialLinearGroup.map σ A) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_conjSLn, coe_conjSLn,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    Matrix.map_mul, Matrix.map_mul, ← Matrix.GeneralLinearGroup.map_inv]
  rfl

theorem conjSLn_diagGLn (d : Fin n → Kˣ) (A : SL(n, K)) :
    conjSLn (CFSG.RankThree.PartOne.KE.diagGLn d) A = CFSG.RankThree.PartOne.KE.conjDiagn d A := by
  apply Subtype.ext
  rw [coe_conjSLn, CFSG.RankThree.PartOne.KE.coe_conjDiagn]

end CFSG.RankThree.Classical2
