module

public import CFSG.Monster.SteinbergMY443NativeSurjective
public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.YGroups.Y443.Native.Image

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster.Generated CFSG.Open

theorem simple_presentation_M_native_surjection_isomorphism :
    ∀ f : MonsterY443Derived →* Gmat, IsFM f → IsSimpleGroup MonsterY443Derived →
      f.ker = ⊥ ∧ Function.Bijective f ∧ Finite MonsterY443Derived := by
  intro f hf _
  obtain ⟨-, -, -, -, -, -, hker, -⟩ := y443_derived_nontrivial_finite_image.2 f hf
  have hbot : f.ker = ⊥ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker).resolve_right hker
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hbot
  exact ⟨hbot, ⟨hinj, (y443_native_surjective_homomorphism.1 f hf).1⟩, Finite.of_injective f hinj⟩

theorem simple_presentation_M_native_surjection_isomorphism_catalog
    (hsimple : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M) :
    Function.Bijective (fM.comp Sporadic.Bridge.Y443.commutatorMulEquiv.toMonoidHom) ∧
      Finite CFSG.Blueprint.NativeSporadic.M := by
  have hs : IsSimpleGroup MonsterY443Derived :=
    Sporadic.Bridge.Y443.commutatorMulEquiv.symm.isSimpleGroup
  obtain ⟨-, hb, hfin⟩ := simple_presentation_M_native_surjection_isomorphism fM fM_isFM hs
  refine ⟨hb.comp Sporadic.Bridge.Y443.commutatorMulEquiv.bijective, ?_⟩
  exact Finite.of_injective Sporadic.Bridge.Y443.commutatorMulEquiv
    Sporadic.Bridge.Y443.commutatorMulEquiv.injective

end CFSG.YGroups.Y443
