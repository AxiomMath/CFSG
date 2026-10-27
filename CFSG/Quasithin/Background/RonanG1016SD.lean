module

public import CFSG.Quasithin.Background.G11Bridge

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem SelfDual.mono {K K' : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} (h : K ≤ K')
    (hs : SelfDual K' I) : SelfDual K I := by
  obtain ⟨f, hnd, hinv⟩ := hs
  exact ⟨f, hnd, fun k hk => hinv k (h hk)⟩

theorem selfDual_of_hiso {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V}
    (hI : Invariant H I) (hiso : HIso H I J) (hs : SelfDual H I) : SelfDual H J := by
  obtain ⟨ψ, hψ⟩ := HIso.symm hI hiso
  obtain ⟨f, hnd, hinv⟩ := hs
  refine ⟨LinearMap.BilinForm.congr ψ.symm f,
    LinearMap.BilinForm.Nondegenerate.congr ψ.symm hnd, fun k hk i j i' j' hki hkj => ?_⟩
  rw [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.congr_apply]
  simp only [LinearEquiv.symm_symm]
  exact hinv k hk (ψ i) (ψ j) (ψ i') (ψ j') (hψ k hk i i' hki) (hψ k hk j j' hkj)

theorem selfDual_conjSub {H : Subgroup (GLV V)} {γ : GLV V} (hγ : ∀ k ∈ H, γ⁻¹ * k * γ ∈ H)
    {I : Submodule (ZMod 2) V} (hs : SelfDual H I) : SelfDual H (conjSub γ I) := by
  obtain ⟨f, hnd, hinv⟩ := hs
  let c : ↥I ≃ₗ[ZMod 2] ↥(conjSub γ I) :=
    LinearEquiv.ofSubmodules (γ : V ≃ₗ[ZMod 2] V) I (conjSub γ I) rfl
  have hc : ∀ x : ↥I, ((c x : ↥(conjSub γ I)) : V) = γ (x : V) := fun x => rfl
  have key : ∀ (k : GLV V) (z z' : ↥(conjSub γ I)), k (z : V) = (z' : V) →
      (γ⁻¹ * k * γ) ((c.symm z : ↥I) : V) = ((c.symm z' : ↥I) : V) := by
    intro k z z' hz
    have h1 : γ ((c.symm z : ↥I) : V) = (z : V) := by
      rw [← hc, LinearEquiv.apply_symm_apply]
    have h2 : γ ((c.symm z' : ↥I) : V) = (z' : V) := by
      rw [← hc, LinearEquiv.apply_symm_apply]
    show γ⁻¹ (k (γ ((c.symm z : ↥I) : V))) = _
    rw [h1, hz, ← h2]
    exact LinearEquiv.symm_apply_apply γ _
  refine ⟨LinearMap.BilinForm.congr c f, LinearMap.BilinForm.Nondegenerate.congr c hnd,
    fun k hk i j i' j' hki hkj => ?_⟩
  rw [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.congr_apply]
  exact hinv (γ⁻¹ * k * γ) (hγ k hk) (c.symm i) (c.symm j) (c.symm i') (c.symm j')
    (key k i i' hki) (key k j j' hkj)

end G11

end CFSG.Quasithin
