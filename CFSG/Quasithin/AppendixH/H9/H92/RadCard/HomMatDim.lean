module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

theorem finrank_matrix_of_mulVec_mem_and_kills {K : Type*} [Field K] {n : ℕ}
    (D' E : Submodule K (Fin n → K)) (S : Submodule K (Matrix (Fin n) (Fin n) K))
    (hS : ∀ N, N ∈ S ↔ (∀ x : Fin n → K, N *ᵥ x ∈ D') ∧ ∀ u ∈ E, N *ᵥ u = 0) :
    Module.finrank K S = (n - Module.finrank K E) * Module.finrank K D' := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl E
  set P : (Fin n → K) →ₗ[K] C := C.projectionOnto E hC.symm
  have hPc : ∀ c : C, P (c : Fin n → K) = c :=
    fun c => Submodule.projectionOnto_apply_left _ c
  have hPE : ∀ x : Fin n → K, x - (P x : Fin n → K) ∈ E := by
    intro x
    refine (Submodule.projectionOnto_apply_eq_zero_iff hC.symm).1 ?_
    rw [map_sub, hPc, sub_self]
  have hΨ : ∀ (f : C →ₗ[K] D') (x : Fin n → K),
      (Matrix.toLin'.symm (D'.subtype ∘ₗ f ∘ₗ P)) *ᵥ x = (f (P x) : Fin n → K) := by
    intro f x
    rw [← Matrix.toLin'_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hΨmem : ∀ f : C →ₗ[K] D', Matrix.toLin'.symm (D'.subtype ∘ₗ f ∘ₗ P) ∈ S := by
    intro f
    refine (hS _).2 ⟨fun x => ?_, fun u hu => ?_⟩
    · rw [hΨ]
      exact (f (P x)).2
    · rw [hΨ, (Submodule.projectionOnto_apply_eq_zero_iff hC.symm).2 hu, map_zero]
      rfl
  let Φ : S →ₗ[K] (C →ₗ[K] D') :=
    { toFun := fun N => LinearMap.codRestrict D'
        ((Matrix.mulVecLin (N : Matrix (Fin n) (Fin n) K)).comp C.subtype)
        (fun c => ((hS N).1 N.2).1 c)
      map_add' := fun N N' => by
        refine LinearMap.ext fun c => Subtype.ext ?_
        change ((N + N' : S) : Matrix (Fin n) (Fin n) K) *ᵥ (c : Fin n → K) =
          (N : Matrix (Fin n) (Fin n) K) *ᵥ (c : Fin n → K) +
            (N' : Matrix (Fin n) (Fin n) K) *ᵥ (c : Fin n → K)
        rw [Submodule.coe_add, Matrix.add_mulVec]
      map_smul' := fun a N => by
        refine LinearMap.ext fun c => Subtype.ext ?_
        change ((a • N : S) : Matrix (Fin n) (Fin n) K) *ᵥ (c : Fin n → K) =
          a • ((N : Matrix (Fin n) (Fin n) K) *ᵥ (c : Fin n → K))
        rw [Submodule.coe_smul, Matrix.smul_mulVec] }
  let e : S ≃ₗ[K] (C →ₗ[K] D') :=
    { Φ with
      invFun := fun f => ⟨Matrix.toLin'.symm (D'.subtype ∘ₗ f ∘ₗ P), hΨmem f⟩
      left_inv := fun N => by
        apply Subtype.ext
        rw [LinearEquiv.symm_apply_eq]
        refine LinearMap.ext fun x => ?_
        change (N : Matrix (Fin n) (Fin n) K) *ᵥ ((P x : C) : Fin n → K) =
          Matrix.toLin' (N : Matrix (Fin n) (Fin n) K) x
        rw [Matrix.toLin'_apply]
        have h0 := ((hS N).1 N.2).2 _ (hPE x)
        rw [Matrix.mulVec_sub, sub_eq_zero] at h0
        exact h0.symm
      right_inv := fun f => by
        refine LinearMap.ext fun c => Subtype.ext ?_
        change (Matrix.toLin'.symm (D'.subtype ∘ₗ f ∘ₗ P)) *ᵥ (c : Fin n → K) =
          (f c : Fin n → K)
        rw [hΨ, hPc] }
  rw [e.finrank_eq, Module.finrank_linearMap]
  have h := Submodule.finrank_add_eq_of_isCompl hC
  rw [Module.finrank_fin_fun] at h
  have hCd : Module.finrank K C = n - Module.finrank K E := by omega
  rw [hCd]

end CFSG.ASVolI.ChH
