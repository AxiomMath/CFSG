module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped TensorProduct

lemma w183b2_tensor_map_one_injective {k : Type*} [Field k] {U₁ U₂ : Type*}
    [AddCommGroup U₁] [Module k U₁] [AddCommGroup U₂] [Module k U₂] [Nontrivial U₂] :
    Function.Injective
      (fun X : Module.End k U₁ => TensorProduct.map X (1 : Module.End k U₂)) := by
  intro X X' h
  obtain ⟨v, hv⟩ := exists_ne (0 : U₂)
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k hv
  ext u
  have h2 := congrArg (fun F : Module.End k (U₁ ⊗[k] U₂) =>
    (TensorProduct.rid k U₁)
      (TensorProduct.map (LinearMap.id : U₁ →ₗ[k] U₁) ψ (F (u ⊗ₜ[k] v)))) h
  simpa [TensorProduct.map_tmul, hψ] using h2

lemma w183b2_tensor_map_one_injective_right {k : Type*} [Field k] {U₁ U₂ : Type*}
    [AddCommGroup U₁] [Module k U₁] [AddCommGroup U₂] [Module k U₂] [Nontrivial U₁] :
    Function.Injective
      (fun Y : Module.End k U₂ => TensorProduct.map (1 : Module.End k U₁) Y) := by
  intro Y Y' h
  obtain ⟨u, hu⟩ := exists_ne (0 : U₁)
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k hu
  ext v
  have h2 := congrArg (fun F : Module.End k (U₁ ⊗[k] U₂) =>
    (TensorProduct.lid k U₂)
      (TensorProduct.map ψ (LinearMap.id : U₂ →ₗ[k] U₂) (F (u ⊗ₜ[k] v)))) h
  simpa [TensorProduct.map_tmul, hψ] using h2

lemma w183b2_toMatrix_map_map {k : Type*} [Field k] {U : Type*} [AddCommGroup U] [Module k U]
    {n : ℕ} (b : Module.Basis (Fin n) k U) (φ : U ≃ₗ[k] U)
    (P : Matrix.GeneralLinearGroup (Fin n) k)
    (hφ : LinearMap.toMatrix b b (φ : U →ₗ[k] U) =
      ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (f : Module.End k U) :
    LinearMap.toMatrix (b.map φ) (b.map φ) f =
      ((P : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        LinearMap.toMatrix b b f *
        ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  have hsymm : LinearMap.toMatrix b b (φ.symm : U →ₗ[k] U) =
      ((P : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    have h1 : LinearMap.toMatrix b b (φ.symm : U →ₗ[k] U) *
        LinearMap.toMatrix b b (φ : U →ₗ[k] U) = 1 := by
      rw [← LinearMap.toMatrix_mul]
      have hcomp : (φ.symm : U →ₗ[k] U) * (φ : U →ₗ[k] U) = 1 := by
        ext x
        simp [Module.End.mul_apply]
      rw [hcomp, LinearMap.toMatrix_one]
    rw [hφ] at h1
    calc LinearMap.toMatrix b b (φ.symm : U →ₗ[k] U)
        = LinearMap.toMatrix b b (φ.symm : U →ₗ[k] U) * 1 := (mul_one _).symm
      _ = LinearMap.toMatrix b b (φ.symm : U →ₗ[k] U) *
            (((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
              ((P : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
            rw [show ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
                ((P : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 from by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
      _ = (LinearMap.toMatrix b b (φ.symm : U →ₗ[k] U) *
              ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) *
              ((P : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
            rw [mul_assoc]
      _ = 1 * ((P : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by rw [h1]
      _ = ((P : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := one_mul _
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  rw [show (φ.symm : U →ₗ[k] U) ∘ₗ (f ∘ₗ (φ : U →ₗ[k] U)) =
      (φ.symm : U →ₗ[k] U) * f * (φ : U →ₗ[k] U) by
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    rfl]
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hsymm, hφ, mul_assoc]

end CFSG.LocalAnalysis.WeakClosure81

end
