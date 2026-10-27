module

public import CFSG.Mathlib.LinearAlgebra.RootSystem.TorusStabilizer

public noncomputable section

namespace CFSG.RootPairing

variable {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y] [Module.Free ℤ X]
  [Module.Finite ℤ X] (P : _root_.RootPairing ι ℤ X Y)

lemma eq_zero_of_apply_root_eq_zero (hsc : P.corootSpan ℤ = ⊤) {g : Module.Dual ℤ X}
    (hg : ∀ i, g (P.root i) = 0) : g = 0 := by
  have := isRootSystem_ratFlip P hsc
  let g' : X →ₗ[ℤ] ℚ := Algebra.linearMap ℤ ℚ ∘ₗ g
  have hle : Submodule.span ℚ (Set.range (ratFlip P).coroot) ≤
      LinearMap.ker (Module.Dual.eval ℚ (X →ₗ[ℤ] ℚ) g') := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [g', hg]
  have h0 : g' = 0 := (Module.forall_dual_apply_eq_zero_iff ℚ g').mp fun φ => by
    have hφ : φ ∈ Submodule.span ℚ (Set.range (ratFlip P).coroot) := by
      rw [_root_.RootPairing.IsRootSystem.span_coroot_eq_top]
      exact Submodule.mem_top
    simpa using hle hφ
  ext x
  simpa [g'] using LinearMap.congr_fun h0 x

variable {P}

lemma coroot'_comp_of_root_perm (hsc : P.corootSpan ℤ = ⊤) {f : X ≃ₗ[ℤ] X} {e : ι ≃ ι}
    (hf : ∀ i, f (P.root i) = P.root (e i)) (i : ι) :
    P.coroot' i ∘ₗ f.toLinearMap = P.coroot' (e.symm i) := by
  have hrefl : ∀ (j : ι) (x : X), Module.preReflection (P.root j) (P.coroot' j) x =
      P.reflection j x := fun j x => by
    rw [Module.preReflection_apply, P.reflection_apply]
  have h₁ : (P.coroot' i ∘ₗ f.toLinearMap) (P.root (e.symm i)) = 2 := by
    simp [hf, P.root_coroot'_eq_pairing]
  have h₁' : Set.MapsTo (Module.preReflection (P.root (e.symm i)) (P.coroot' i ∘ₗ f.toLinearMap))
      (Set.range P.root) (Set.range P.root) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨e.symm (P.reflectionPerm i (e j)), f.injective ?_⟩
    simp only [hf, Equiv.apply_symm_apply, P.root_reflectionPerm, Module.preReflection_apply,
      map_sub, map_smul, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      P.reflection_apply]
  have h₂ : P.coroot' (e.symm i) (P.root (e.symm i)) = 2 := by
    simp [P.root_coroot'_eq_pairing]
  have h₂' : Set.MapsTo (Module.preReflection (P.root (e.symm i)) (P.coroot' (e.symm i)))
      (Set.range P.root) (Set.range P.root) := fun x hx => by
    rw [hrefl]
    exact P.mapsTo_reflection_root _ hx
  have h := Module.Dual.eq_of_preReflection_mapsTo' (Set.finite_range P.root)
    (Submodule.subset_span ⟨_, rfl⟩) h₁ h₁' h₂ h₂'
  rw [← sub_eq_zero]
  refine eq_zero_of_apply_root_eq_zero P hsc fun j => ?_
  have hj := LinearMap.congr_fun h ⟨P.root j, Submodule.subset_span ⟨j, rfl⟩⟩
  simp only [LinearMap.dualMap_apply, LinearMap.coe_comp, Function.comp_apply,
    Submodule.subtype_apply] at hj
  rw [LinearMap.sub_apply, LinearMap.comp_apply, hj, sub_self]

variable (P)

@[expose] def autOfRootPerm (hsc : P.corootSpan ℤ = ⊤) (f : X ≃ₗ[ℤ] X) (e : ι ≃ ι)
    (hf : ∀ i, f (P.root i) = P.root (e i)) : P.Aut where
  weightMap := f
  coweightMap := P.flip.toPerfPair.trans (f.dualMap.trans P.flip.toPerfPair.symm)
  indexEquiv := e
  weight_coweight_transpose := by ext; simp
  root_weightMap := by ext; simp [hf]
  coroot_coweightMap := by
    funext i
    simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
    rw [LinearEquiv.symm_apply_eq]
    ext x
    simpa using LinearMap.congr_fun (coroot'_comp_of_root_perm hsc hf i) x
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

variable {P}

@[simp]
lemma autOfRootPerm_indexEquiv (hsc : P.corootSpan ℤ = ⊤) (f : X ≃ₗ[ℤ] X) (e : ι ≃ ι)
    (hf : ∀ i, f (P.root i) = P.root (e i)) : (autOfRootPerm P hsc f e hf).indexEquiv = e :=
  rfl

@[simp]
lemma autOfRootPerm_smul (hsc : P.corootSpan ℤ = ⊤) (f : X ≃ₗ[ℤ] X) (e : ι ≃ ι)
    (hf : ∀ i, f (P.root i) = P.root (e i)) (x : X) : autOfRootPerm P hsc f e hf • x = f x :=
  rfl

end CFSG.RootPairing
