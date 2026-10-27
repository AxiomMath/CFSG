module

public import CFSG.Quasithin.AppendixH.H9.H92.RadDefs

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

private theorem gl_mulVec_inv_mulVec {n : ℕ} (B : GL (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      (((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

private theorem conj_mem_radMat {n : ℕ} {D₁ D₂ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (B : GL (Fin n) (ZMod 2))
    (hB : ∀ x, (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x ∈ D₂ ↔ x ∈ D₁)
    {C : GL (Fin n) (ZMod 2)} (hC : C ∈ RadMat n D₁) : B * C * B⁻¹ ∈ RadMat n D₂ := by
  obtain ⟨hC1, hC2⟩ := hC
  refine ⟨fun x => ?_, fun u hu => ?_⟩
  · have h := (hB _).mpr
      (hC1 (((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x))
    have e : (((B * C * B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x =
        (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
          (((C : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ
            (((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_sub, gl_mulVec_inv_mulVec, Units.val_mul, Units.val_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [e]
    exact h
  · have hd : ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u ∈ D₁ := by
      rw [← hB, gl_mulVec_inv_mulVec]
      exact hu
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hC2 _ hd,
      gl_mulVec_inv_mulVec]

theorem map_conj_radMat {n : ℕ} {D₁ D₂ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (B : GL (Fin n) (ZMod 2))
    (hB : ∀ x, (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x ∈ D₂ ↔ x ∈ D₁) :
    (RadMat n D₁).map (MulAut.conj B).toMonoidHom = RadMat n D₂ := by
  apply le_antisymm
  · rintro _ ⟨C, hC, rfl⟩
    exact conj_mem_radMat B hB hC
  · intro C hC
    have hB' : ∀ x, ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x ∈ D₁ ↔
        x ∈ D₂ := by
      intro x
      rw [← hB, gl_mulVec_inv_mulVec]
    refine ⟨B⁻¹ * C * B, conj_mem_radMat B⁻¹ hB' hC, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem exists_linearEquiv_map_submodule_eq {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {D₁ D₂ : Submodule K V}
    (h : Module.finrank K D₁ = Module.finrank K D₂) :
    ∃ g : V ≃ₗ[K] V, ∀ x, g x ∈ D₂ ↔ x ∈ D₁ := by
  let f : D₁ ≃ₗ[K] D₂ := LinearEquiv.ofFinrankEq D₁ D₂ h
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨y, hy⟩ := f.surjective ⟨g x, hx⟩
    have h1 : g (y : V) = g x := by rw [← hg y, hy]
    have h2 : (y : V) = x := g.injective h1
    rw [← h2]
    exact y.2
  · rw [← hg ⟨x, hx⟩]
    exact (f ⟨x, hx⟩).2

private theorem exists_linearEquiv_map_submodule_eq_zmod {n : ℕ}
    {D₁ D₂ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (h : Module.finrank (ZMod 2) D₁ = Module.finrank (ZMod 2) D₂) :
    ∃ g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2), ∀ x, g x ∈ D₂ ↔ x ∈ D₁ := by
  exact @exists_linearEquiv_map_submodule_eq (ZMod 2) (Fin n → ZMod 2) _ _
    (inferInstanceAs (Module (ZMod 2) (Fin n → ZMod 2))) inferInstance D₁ D₂ h

theorem exists_gl_mulVec_eq_linearEquiv {n : ℕ}
    (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    ∃ B : GL (Fin n) (ZMod 2), ∀ x, (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = g x := by
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv g), fun x => ?_⟩
  have h := Matrix.GeneralLinearGroup.toLin_apply
    (Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv g)) x
  rw [MulEquiv.apply_symm_apply] at h
  simpa using h.symm

theorem exists_gl_map_submodule_eq {n : ℕ} {D₁ D₂ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (h : Module.finrank (ZMod 2) D₁ = Module.finrank (ZMod 2) D₂) :
    ∃ B : GL (Fin n) (ZMod 2),
      ∀ x, (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x ∈ D₂ ↔ x ∈ D₁ := by
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_submodule_eq_zmod h
  obtain ⟨B, hB⟩ := exists_gl_mulVec_eq_linearEquiv g
  exact ⟨B, fun x => by rw [hB x]; exact hg x⟩

end CFSG.ASVolI.ChH
