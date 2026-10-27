module

public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.Monster.SteinbergMY443NativeSurjective
public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.YGroups.Y443.Native.Image

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.Monster.Generated CFSG.Open CFSG.YGroups.Y443

theorem isFM_comp_mulEquiv_bijective
    {f : MonsterY443Derived →* Gmat} (hf : IsFM f)
    {F : Type*} [Group F] [IsSimpleGroup F] (θ : F ≃* MonsterY443Derived) :
    Function.Bijective (f.comp θ.toMonoidHom) := by
  have hs : Function.Surjective f := (y443_native_surjective_homomorphism.1 f hf).1
  have h3 : orderOf (f (axElt y443U11)) = 3 := (y443_derived_nontrivial_finite_image.2 f hf).2.1
  refine bijective_of_surjective_of_isSimpleGroup _ (hs.comp θ.surjective)
    ⟨θ.symm (axElt y443U11), fun h => ?_⟩
  have h' : f (axElt y443U11) = 1 := by
    simpa only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using h
  rw [h', orderOf_one] at h3
  exact absurd h3 (by norm_num)

theorem catalog_fM_comp_mulEquiv_bijective
    {F : Type*} [Group F] [IsSimpleGroup F]
    (θ : F ≃* CFSG.Blueprint.NativeSporadic.M) :
    Function.Bijective
      ((fM.comp CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toMonoidHom).comp θ.toMonoidHom) :=
  isFM_comp_mulEquiv_bijective fM_isFM (θ.trans CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv)

theorem simple_catalog_M_native_isomorphism :
    (∀ f : MonsterY443Derived →* Gmat, IsFM f →
      ∀ (F : Type*) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
        ∀ θ : F ≃* MonsterY443Derived, Function.Bijective (f.comp θ.toMonoidHom)) ∧
    ∀ (F : Type*) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
      ∀ θ : F ≃* CFSG.Blueprint.NativeSporadic.M,
        Function.Bijective
          ((fM.comp CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toMonoidHom).comp
            θ.toMonoidHom) :=
  ⟨fun _ hf _ _ _ _ _ θ => isFM_comp_mulEquiv_bijective hf θ,
    fun _ _ _ _ _ θ => catalog_fM_comp_mulEquiv_bijective θ⟩

end CFSG.ComponentClassification.BMCase
