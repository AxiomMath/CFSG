module

public import CFSG.Quasithin.Background.G117Top

public section

namespace CFSG.Quasithin

namespace G11

namespace G117

open scoped TensorProduct

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isL28TwistedTensorModule_of_restrictRange_top {K : Subgroup (GLV V)}
    (h : IsL28TwistedTensorModule (restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K))) :
    IsL28TwistedTensorModule K := by
  obtain ⟨φ, ψ, hψ⟩ := h
  let e : V ≃ₗ[ZMod 2] ↥(⊤ : Submodule (ZMod 2) V) :=
    (Submodule.topEquiv (R := ZMod 2) (M := V)).symm
  let T : Type := ↥(⊤ : Submodule (ZMod 2) V)
  refine ⟨(restrictRangeTop K).trans φ,
    (e.baseChange (ZMod 2) (GaloisField 2 3) V T).trans ψ, fun k x => ?_⟩
  let k' : GLV T :=
    ((restrictRangeTop K k : ↥(restrictRange K (⊤ : Submodule (ZMod 2) V) (invariant_top K))) :
      GLV T)
  have hk : (e : V →ₗ[ZMod 2] T) ∘ₗ ((k : GLV V) : V →ₗ[ZMod 2] V) =
      (k' : T →ₗ[ZMod 2] T) ∘ₗ (e : V →ₗ[ZMod 2] T) :=
    LinearMap.ext fun v => Subtype.ext rfl
  have hb : e.baseChange (ZMod 2) (GaloisField 2 3) V T
      (LinearMap.baseChange (GaloisField 2 3) ((k : GLV V) : V →ₗ[ZMod 2] V) x) =
      LinearMap.baseChange (GaloisField 2 3) (k' : T →ₗ[ZMod 2] T)
        (e.baseChange (ZMod 2) (GaloisField 2 3) V T x) := by
    have h1 := congrArg (fun f => LinearMap.baseChange (GaloisField 2 3) f x) hk
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at h1
    exact h1
  simp only [LinearEquiv.trans_apply]
  rw [hb]
  exact hψ (restrictRangeTop K k) _

end G117

end G11

end CFSG.Quasithin
