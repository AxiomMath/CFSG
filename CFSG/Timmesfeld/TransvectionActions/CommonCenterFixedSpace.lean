module


public import CFSG.Timmesfeld.TransvectionActions.CommonCenterDual

import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Timmesfeld.TransvectionActions

variable {ActingGroup : Type*} [Group ActingGroup] {Space : Type*}
  [AddCommGroup Space] [Module (ZMod 2) Space]
  {action : Representation (ZMod 2) ActingGroup Space} {center : Space}

theorem displacementFunctional_injective (commonCenter : CommonTransvectionCenter action center)
    (elementary : IsElementaryAbelian2 ActingGroup) :
    Function.Injective (displacementFunctional commonCenter) := fun first second coefficientsEq =>
  displacementHom_injective commonCenter elementary (by simp [displacementHom, coefficientsEq])

theorem finrank_fixedSpace_univ_of_commonTransvectionCenter [Module.Finite (ZMod 2) Space]
    (groupRank : ℕ) (groupCard : Nat.card ActingGroup = 2 ^ groupRank)
    (elementary : IsElementaryAbelian2 ActingGroup)
    (commonCenter : CommonTransvectionCenter action center) :
    groupRank ≤ Module.finrank (ZMod 2) Space ∧
      Module.finrank (ZMod 2) (fixedSpace action Set.univ) =
        Module.finrank (ZMod 2) Space - groupRank := by
  have groupFinite : Finite ActingGroup := Nat.finite_of_card_ne_zero (by rw [groupCard]; positivity)
  have imageRank : Module.finrank (ZMod 2) (displacementImage commonCenter elementary) =
      groupRank := by
    have imageCard : Nat.card (displacementImage commonCenter elementary) = Nat.card ActingGroup := by
      have imageRangeCard : Nat.card (displacementImage commonCenter elementary) =
          Nat.card (Set.range (displacementFunctional commonCenter)) := rfl
      rw [imageRangeCard, Nat.card_range_of_injective
        (displacementFunctional_injective commonCenter elementary)]
    have rankCard := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := displacementImage commonCenter elementary)
    rw [imageCard, groupCard, Nat.card_zmod] at rankCard
    exact (Nat.pow_right_injective (le_refl 2) rankCard).symm
  have fixedCoannihilator : fixedSpace action Set.univ =
      (displacementImage commonCenter elementary).dualCoannihilator := by
    ext vector
    rw [Submodule.mem_dualCoannihilator, mem_fixedSpace]
    constructor
    · rintro vectorFixed functional functionalMem
      obtain ⟨element, rfl⟩ := (mem_displacementImage commonCenter elementary functional).1 functionalMem
      have coefficientIdentity := displacementFunctional_smul commonCenter element vector
      rw [vectorFixed element (Set.mem_univ element), sub_self] at coefficientIdentity
      exact (smul_eq_zero.mp coefficientIdentity).resolve_right commonCenter.ne_zero
    · intro coefficientsZero element _
      have coefficientIdentity := displacementFunctional_smul commonCenter element vector
      rw [coefficientsZero _ ((mem_displacementImage commonCenter elementary _).2 ⟨element, rfl⟩),
        zero_smul] at coefficientIdentity
      exact sub_eq_zero.mp coefficientIdentity.symm
  have rankNullity := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (displacementImage commonCenter elementary)
  rw [← fixedCoannihilator, imageRank] at rankNullity
  omega

end CFSG.Timmesfeld.TransvectionActions
