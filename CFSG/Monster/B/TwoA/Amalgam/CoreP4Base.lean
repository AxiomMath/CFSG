
module

public import CFSG.Monster.B.TwoA.Sp8.QuadForm
public import CFSG.Monster.B.TwoA.Sp8.Orth8PairsBase
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

abbrev SingV : Type := {v : V8 // qPoly v = 0 ∧ v ≠ 0}

theorem qPoly_orth {M : V8 ≃ₗ[ZMod 2] V8} (hM : M ∈ TauCeti.QuadraticMap.orthogonalGroup qForm)
    (v : V8) : qPoly (M v) = qPoly v := by
  have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hM v
  rwa [qForm_apply, qForm_apply] at h

@[expose, instance_reducible] def singAction :
    MulAction (TauCeti.QuadraticMap.orthogonalGroup qForm) SingV where
  smul M v := ⟨(M : V8 ≃ₗ[ZMod 2] V8) v.1, by rw [qPoly_orth M.2]; exact v.2.1,
    fun h => v.2.2 (((M : V8 ≃ₗ[ZMod 2] V8).map_eq_zero_iff).1 h)⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem natCard_SingV : Nat.card SingV = 119 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem singAction_faithful :
    @FaithfulSMul (TauCeti.QuadraticMap.orthogonalGroup qForm) SingV singAction.toSMul := by
  let _ := singAction
  refine ⟨fun {M N} h => ?_⟩
  have hs : ∀ v : V8, qPoly v = 0 →
      (M : V8 ≃ₗ[ZMod 2] V8) v = (N : V8 ≃ₗ[ZMod 2] V8) v := by
    intro v hv
    by_cases h0 : v = 0
    · rw [h0, map_zero, map_zero]
    · exact congrArg Subtype.val (h ⟨v, hv, h0⟩)
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext fun i x => ?_
  rcases zmod2_cases x with rfl | rfl
  · rw [Pi.single_zero, map_zero, map_zero]
  · obtain ⟨a, b, ha, hb, hab⟩ := zeros_span i
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← hab, map_add, map_add, hs a ha, hs b hb]

end CFSG.Monster.B.TwoA.Sp8
