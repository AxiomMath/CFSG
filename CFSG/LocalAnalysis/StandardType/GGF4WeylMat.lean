module

public import CFSG.LocalAnalysis.StandardType.GGF4WeylData
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.F4Model

@[expose] def M4.toMat (x : M4) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![x.m00, x.m01, x.m02, x.m03; x.m10, x.m11, x.m12, x.m13;
    x.m20, x.m21, x.m22, x.m23; x.m30, x.m31, x.m32, x.m33]

theorem M4.toMat_mul (x y : M4) : (x.mul y).toMat = x.toMat * y.toMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
    | (simp [M4.toMat, M4.mul, Matrix.mul_apply, Fin.sum_univ_four]; done)
    | (simp [M4.toMat, M4.mul, Matrix.mul_apply, Fin.sum_univ_four]; ring)

theorem M4.toMat_one : M4.one.toMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M4.toMat, M4.one, Matrix.one_apply]

theorem M4.ext' {x y : M4} (h00 : x.m00 = y.m00) (h01 : x.m01 = y.m01) (h02 : x.m02 = y.m02)
    (h03 : x.m03 = y.m03) (h10 : x.m10 = y.m10) (h11 : x.m11 = y.m11) (h12 : x.m12 = y.m12)
    (h13 : x.m13 = y.m13) (h20 : x.m20 = y.m20) (h21 : x.m21 = y.m21) (h22 : x.m22 = y.m22)
    (h23 : x.m23 = y.m23) (h30 : x.m30 = y.m30) (h31 : x.m31 = y.m31) (h32 : x.m32 = y.m32)
    (h33 : x.m33 = y.m33) : x = y := by
  cases x
  cases y
  first
  | (simp_all; done)
  | (dsimp only at *; subst_vars; rfl)

theorem M4.toMat_injective : Function.Injective M4.toMat := by
  intro x y h
  have e : ∀ i j, x.toMat i j = y.toMat i j := fun i j => by rw [h]
  exact M4.ext' (by simpa [M4.toMat] using e 0 0) (by simpa [M4.toMat] using e 0 1)
    (by simpa [M4.toMat] using e 0 2) (by simpa [M4.toMat] using e 0 3)
    (by simpa [M4.toMat] using e 1 0) (by simpa [M4.toMat] using e 1 1)
    (by simpa [M4.toMat] using e 1 2) (by simpa [M4.toMat] using e 1 3)
    (by simpa [M4.toMat] using e 2 0) (by simpa [M4.toMat] using e 2 1)
    (by simpa [M4.toMat] using e 2 2) (by simpa [M4.toMat] using e 2 3)
    (by simpa [M4.toMat] using e 3 0) (by simpa [M4.toMat] using e 3 1)
    (by simpa [M4.toMat] using e 3 2) (by simpa [M4.toMat] using e 3 3)

theorem M4.toMat_pw2 (z : M4) : (pw2 z).toMat = z.toMat * z.toMat := by
  rw [pw2, M4.toMat_mul]

theorem M4.toMat_pw3 (z : M4) : (pw3 z).toMat = z.toMat * (z.toMat * z.toMat) := by
  rw [pw3, M4.toMat_mul, M4.toMat_mul]

theorem M4.toMat_pw4 (z : M4) :
    (pw4 z).toMat = z.toMat * z.toMat * (z.toMat * z.toMat) := by
  rw [pw4, M4.toMat_mul, M4.toMat_mul]

end CFSG.StandardType.F4Model

end
