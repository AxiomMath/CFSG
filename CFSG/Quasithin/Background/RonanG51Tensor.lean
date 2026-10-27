module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Quasithin.RonanG51

open scoped TensorProduct Matrix

variable (F : Type) [Field F] [Algebra (ZMod 2) F] {V : Type} [AddCommGroup V]
  [Module (ZMod 2) V] {n : ℕ} (e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2))

noncomputable def theta : (F ⊗[ZMod 2] V) ≃ₗ[F] (Fin n → F) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl F F) e).trans
    (TensorProduct.piScalarRight (ZMod 2) F F (Fin n))

theorem theta_tmul (x : F) (v : V) : theta F e (x ⊗ₜ[ZMod 2] v) = fun i => e v i • x := by
  simp [theta]

theorem theta_lTensor (f : V →ₗ[ZMod 2] V) (K : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ v, e (f v) = K *ᵥ e v) (w : F ⊗[ZMod 2] V) :
    theta F e (LinearMap.lTensor F f w) = (K.map (algebraMap (ZMod 2) F)) *ᵥ theta F e w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
    rw [LinearMap.lTensor_tmul, theta_tmul, theta_tmul, hf]
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc, Algebra.smul_def]
  | add a b ha hb => simp [map_add, Matrix.mulVec_add, ha, hb]

theorem theta_rTensor (g : F →ₗ[ZMod 2] F) (w : F ⊗[ZMod 2] V) :
    theta F e (LinearMap.rTensor V g w) = fun i => g (theta F e w i) := by
  induction w using TensorProduct.induction_on with
  | zero => ext i; simp
  | tmul x v =>
    rw [LinearMap.rTensor_tmul, theta_tmul, theta_tmul]
    funext i
    simp [map_smul]
  | add a b ha hb => ext i; simp [map_add, ha, hb]

end CFSG.Quasithin.RonanG51
