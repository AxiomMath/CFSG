module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

public section

namespace CFSG

theorem diagGL_mul_mul_inv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [Field k]
    (e : ι → kˣ) (A : GL ι k) (i j : ι) :
    ((TauCeti.diagGL e * A * (TauCeti.diagGL e)⁻¹ : GL ι k) : Matrix ι ι k) i j =
      (e i : k) * (A : Matrix ι ι k) i j * ((e j : k))⁻¹ := by
  have hD : ((TauCeti.diagGL e : GL ι k) : Matrix ι ι k) =
      Matrix.diagonal (fun i => (e i : k)) := TauCeti.diagGL_coe e
  have hDi : (((TauCeti.diagGL e)⁻¹ : GL ι k) : Matrix ι ι k) =
      Matrix.diagonal (fun i => ((e i)⁻¹ : k)) := by
    rw [← map_inv, TauCeti.diagGL_coe]
    simp
  rw [Units.val_mul, Units.val_mul, hD, hDi, Matrix.mul_diagonal, Matrix.diagonal_mul]

end CFSG
