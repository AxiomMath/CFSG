module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

open CFSG.StandardType CFSG.LieType.Universal

namespace CFSG.StandardType.LieKnownR2.POmega

theorem omegaSmall_ggRootSub_transport {U₁ U₂ G : Type} [Group U₁] [Group U₂] [Group G]
    {Δ₁ : UniversalRootDatum U₁} {Δ₂ : UniversalRootDatum U₂} (e : U₁ ≃* U₂) (φ : U₁ →* G)
    {β : Fin Δ₁.rank → ℤ} {γ : Fin Δ₂.rank → ℤ} (w : U₂)
    (h : (Δ₁.rootGroup β).map e.toMonoidHom = (Δ₂.rootGroup γ).map (MulAut.conj w).toMonoidHom)
    (u : U₁) :
    ggRootSub Δ₁ φ β u = ggRootSub Δ₂ (φ.comp e.symm.toMonoidHom) γ (e u * w) := by
  ext x
  simp only [ggRootSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hz' : e z ∈ (Δ₂.rootGroup γ).map (MulAut.conj w).toMonoidHom := by
      rw [← h]
      exact ⟨z, hz, rfl⟩
    obtain ⟨z', hz'γ, hzz⟩ := hz'
    refine ⟨(MulAut.conj (e u * w)).toMonoidHom z', ⟨z', hz'γ, rfl⟩, ?_⟩
    have hzz' : w * z' * w⁻¹ = e z := by
      first
        | exact hzz
        | simpa using hzz
    have key : e u * w * z' * (e u * w)⁻¹ = e (u * z * u⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← hzz']
      simp only [mul_assoc, mul_inv_rev]
    have hgoal : φ (e.symm (e u * w * z' * (e u * w)⁻¹)) = φ (u * z * u⁻¹) := by
      rw [key, MulEquiv.symm_apply_apply]
    first
      | exact hgoal
      | simpa using hgoal
  · rintro ⟨y, ⟨z', hz', rfl⟩, rfl⟩
    have hz'' : w * z' * w⁻¹ ∈ (Δ₁.rootGroup β).map e.toMonoidHom := by
      rw [h]
      exact ⟨z', hz', rfl⟩
    obtain ⟨z, hzβ, hzz⟩ := hz''
    refine ⟨(MulAut.conj u).toMonoidHom z, ⟨z, hzβ, rfl⟩, ?_⟩
    have hzz' : e z = w * z' * w⁻¹ := by
      first
        | exact hzz
        | simpa using hzz
    have key : e u * w * z' * (e u * w)⁻¹ = e (u * z * u⁻¹) := by
      rw [map_mul, map_mul, map_inv, hzz']
      simp only [mul_assoc, mul_inv_rev]
    have hgoal : φ (u * z * u⁻¹) = φ (e.symm (e u * w * z' * (e u * w)⁻¹)) := by
      rw [key, MulEquiv.symm_apply_apply]
    first
      | exact hgoal
      | simpa using hgoal

theorem omegaSmall_ker_le_center {U₁ U₂ G : Type} [Group U₁] [Group U₂] [Group G]
    (e : U₁ ≃* U₂) (φ : U₁ →* G) (hker : φ.ker ≤ Subgroup.center U₁) :
    (φ.comp e.symm.toMonoidHom).ker ≤ Subgroup.center U₂ := by
  intro x hx
  have hx' : e.symm x ∈ φ.ker := by
    first
      | exact hx
      | simpa [MonoidHom.mem_ker] using hx
  have hc := hker hx'
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro g
  have h2 := congrArg e (hc (e.symm g))
  simpa using h2

theorem omegaSmall_range_eq {U₁ U₂ G : Type} [Group U₁] [Group U₂] [Group G]
    (e : U₁ ≃* U₂) (φ : U₁ →* G) : (φ.comp e.symm.toMonoidHom).range = φ.range := by
  ext x
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    first
      | simp
      | (show φ (e.symm (e y)) = φ y
         rw [MulEquiv.symm_apply_apply])

end CFSG.StandardType.LieKnownR2.POmega

end
