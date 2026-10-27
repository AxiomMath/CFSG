module

public import CFSG.LocalAnalysis.SignalizerFunctor.NormalProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonMaxOrder
import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonCanonical

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem commuting_abelian_sup (first second : Subgroup GroupType)
    (first_abelian : IsMulCommutative first) (second_abelian : IsMulCommutative second)
    (commuting : second ≤ Subgroup.centralizer (first : Set GroupType)) :
    IsMulCommutative (first ⊔ second : Subgroup GroupType) := by
  let := first_abelian
  let := second_abelian
  have normalizes := commuting.trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨⟨?_⟩⟩
  intro firstElement secondElement
  apply Subtype.ext
  obtain ⟨firstLeft, first_left_member, firstRight, first_right_member, first_product⟩ :=
    (mem_sup_of_normalizing first second normalizes firstElement.val).mp firstElement.property
  obtain ⟨secondLeft, second_left_member, secondRight, second_right_member, second_product⟩ :=
    (mem_sup_of_normalizing first second normalizes secondElement.val).mp secondElement.property
  have left_commutes : firstLeft * secondLeft = secondLeft * firstLeft :=
    congrArg Subtype.val (mul_comm' (⟨firstLeft, first_left_member⟩ : first)
      (⟨secondLeft, second_left_member⟩ : first))
  have right_commutes : firstRight * secondRight = secondRight * firstRight :=
    congrArg Subtype.val (mul_comm' (⟨firstRight, first_right_member⟩ : second)
      (⟨secondRight, second_right_member⟩ : second))
  have first_cross := Subgroup.mem_centralizer_iff.mp (commuting first_right_member)
    secondLeft second_left_member
  have second_cross := Subgroup.mem_centralizer_iff.mp (commuting second_right_member)
    firstLeft first_left_member
  change firstElement.val * secondElement.val = secondElement.val * firstElement.val
  rw [← first_product, ← second_product]
  calc
    (firstLeft * firstRight) * (secondLeft * secondRight) =
        firstLeft * (firstRight * secondLeft) * secondRight := by group
    _ = firstLeft * (secondLeft * firstRight) * secondRight := by rw [← first_cross]
    _ = (firstLeft * secondLeft) * (firstRight * secondRight) := by group
    _ = (secondLeft * firstLeft) * (secondRight * firstRight) := by rw [left_commutes, right_commutes]
    _ = secondLeft * (firstLeft * secondRight) * firstRight := by group
    _ = secondLeft * (secondRight * firstLeft) * firstRight := by rw [second_cross]
    _ = (secondLeft * secondRight) * (firstLeft * firstRight) := by group

theorem maximum_order_abelian_self_centralizing (target : Subgroup GroupType)
    (member : target ∈ maximumOrderAbelianFamily GroupType) :
    Subgroup.centralizer (target : Set GroupType) = target :=
  CFSG.centralizer_eq_self_of_mem_maxOrderAbelianFamily
    (CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mp member)

theorem order_thompson_center_eq_intersection :
    orderThompsonCenter GroupType = ⨅ target ∈ maximumOrderAbelianFamily GroupType, target := by
  rw [order_thompson_center_eq_orderZJ, maximum_order_abelian_family_eq_maxOrderAbelianFamily]
  exact CFSG.orderZJ_eq_iInf

theorem center_le_order_thompson_center : Subgroup.center GroupType ≤ orderThompsonCenter GroupType := by
  rw [order_thompson_center_eq_orderZJ]
  exact CFSG.center_le_orderZJ_of_finite

theorem order_thompson_center_pgroup_nontrivial (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType) [Nontrivial GroupType] : orderThompsonCenter GroupType ≠ ⊥ := by
  rw [order_thompson_center_eq_orderZJ]
  exact CFSG.orderZJ_ne_bot_of_isPGroup prime_prime pgroup

end CFSG.SignalizerFunctor.Helpers
