module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import CFSG.LieType.Universal.Spin.Action

public section

namespace CFSG.StandardType.TableC

open CFSG.LieType.Universal

private lemma og_polar_eq_dot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma og_isometry_of_quad {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (M : Matrix ι ι F)
    (hM : ∀ x : ι → F, Q (M.mulVec x) = Q x) :
    M.transpose * LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) * M =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  have hpol : ∀ x y, QuadraticMap.polar Q (M.mulVec x) (M.mulVec y) = QuadraticMap.polar Q x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hM (x + y), hM x, hM y]
  apply (LinearEquiv.injective Matrix.toBilin')
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, ← og_polar_eq_dot Q (M.mulVec x) (M.mulVec y),
    ← og_polar_eq_dot Q x y]
  exact hpol x y

theorem polarGram_transpose {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) :
    Matrix.transpose (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  ext i j
  rw [Matrix.transpose_apply, LinearMap.toMatrix₂'_apply, LinearMap.toMatrix₂'_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_comm]

theorem polarGram_isUnit_det {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.nondegenerate_toMatrix'_iff).mpr hQ))

theorem spinMatrix_isometry {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x : spinGroup Q) :
    Matrix.transpose ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) *
        LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) *
        ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) :=
  og_isometry_of_quad Q _ (Spin.spinMatrix_mem Q x)

end CFSG.StandardType.TableC

end
