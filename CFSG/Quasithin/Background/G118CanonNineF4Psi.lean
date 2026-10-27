module

public import CFSG.Quasithin.Background.G118CanonNineF4S3
public import CFSG.Quasithin.Background.G118CanonNineF4Tensor

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F4Tensor

open scoped TensorProduct

open F2Tensor

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_psi (s : Equiv.Perm (Fin 3) →* GLV V) (hc3 : s rho3 ^ 3 = 1)
    (hfree : ∀ v : V, s rho3 v = v → v = 0) (hyc : s tau3 * s rho3 = (s rho3)⁻¹ * s tau3)
    (hinf : fixSub (s tau3) ⊓ conjSub (s rho3) (fixSub (s tau3)) = ⊥)
    (hsup : fixSub (s tau3) ⊔ conjSub (s rho3) (fixSub (s tau3)) = ⊤)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (lam : ↥(fixSub (s tau3)) ≃ₗ[ZMod 2] W) :
    ∃ ψ : V ≃ₗ[ZMod 2] (↥(permCore 3) ⊗[ZMod 2] W),
      (∀ (π : Equiv.Perm (Fin 3)) (x : ↥(permCore 3)) (a : W),
        ψ (s π (ψ.symm (x ⊗ₜ a))) = permActCore 3 π x ⊗ₜ a) ∧
      (∀ d : GLV V, (∀ v, d (s rho3 v) = s rho3 (d v)) → ∀ a a' : W,
        d ((lam.symm a : ↥(fixSub (s tau3))) : V) = ((lam.symm a' : ↥(fixSub (s tau3))) : V) →
          ∀ x : ↥(permCore 3), ψ (d (ψ.symm (x ⊗ₜ a))) = x ⊗ₜ a') := by
  have hcc : ∀ v, s rho3 (s rho3 v) = s rho3 v + v := sq_eq_add_of_cube (s rho3) hc3 hfree
  let β : W →ₗ[ZMod 2] V := (fixSub (s tau3)).subtype ∘ₗ lam.symm.toLinearMap
  have hβ : ∀ a, β a = ((lam.symm a : ↥(fixSub (s tau3))) : V) := fun a => rfl
  have hβinj : Function.Injective β := Subtype.val_injective.comp lam.symm.injective
  have hβrange : LinearMap.range β = fixSub (s tau3) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (lam.symm a).2
    · intro hv
      exact ⟨lam ⟨v, hv⟩, by rw [hβ, LinearEquiv.symm_apply_apply]⟩
  have hβ0 : ∀ a, s tau3 (β a) = β a := fun a => mem_fixSub.1 (lam.symm a).2
  have hβ1 : ∀ a, s tau3 (s rho3 (β a)) = s rho3 (s rho3 (β a)) := fun a =>
    conj_fixSub_s3 hc3 hyc (lam.symm a).2
  have hβcc : ∀ a, s rho3 (s rho3 (β a)) = s rho3 (β a) + β a := fun a => hcc _
  have hbij := tensorMapW_bijective β (s rho3) (fixSub (s tau3)) hβinj hβrange hinf hsup
  refine ⟨(LinearEquiv.ofBijective (tensorMapW β (s rho3)) hbij).symm, ?_, ?_⟩
  · intro π x a
    rw [LinearEquiv.symm_symm, LinearEquiv.symm_apply_eq]
    exact (tensorMapW_perm β (s rho3) s rfl hβ0 hβ1 hβcc π x a).symm
  · intro d hdc a a' hda x
    rw [LinearEquiv.symm_symm, LinearEquiv.symm_apply_eq]
    exact tensorMapW_comm β (s rho3) d hdc a a' hda x

end F4Tensor

end Canon

end G11

end CFSG.Quasithin
