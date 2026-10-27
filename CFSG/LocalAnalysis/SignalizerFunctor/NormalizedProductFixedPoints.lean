module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProductFixedPoints
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSubfunctorValues
public import CFSG.LocalAnalysis.SignalizerFunctor.ProductPrimeParts

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem normalized_product_fixed_points (prime : ℕ) (prime_prime : prime.Prime)
    (actor parent first second : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (first_normalized : actor ≤ Subgroup.normalizer (first : Set GroupType))
    (second_normalized : actor ≤ Subgroup.normalizer (second : Set GroupType))
    (first_le : first ≤ parent) (second_le : second ≤ parent)
    (coprime : Nat.Coprime prime (Nat.card parent))
    (whole : subgroupProduct first second = (parent : Set GroupType)) :
    subgroupProduct (first ⊓ Subgroup.centralizer (actor : Set GroupType))
      (second ⊓ Subgroup.centralizer (actor : Set GroupType)) =
      ((parent ⊓ Subgroup.centralizer (actor : Set GroupType) : Subgroup GroupType) : Set GroupType) := by
  let _action := conjugationAction actor parent parent_normalized
  apply (subgroup_product_eq_subgroup_iff _ _ _ (inf_le_inf_right _ first_le) (inf_le_inf_right _ second_le)).mpr
  intro element member
  let internalElement : parent := ⟨element, member.1⟩
  have fixed : ∀ actorElement : actor, actorElement • internalElement = internalElement := by
    intro actorElement
    apply Subtype.ext
    change actorElement.val * element * actorElement.val⁻¹ = element
    have commutes := Subgroup.mem_centralizer_iff.mp member.2 actorElement.val actorElement.property
    rw [commutes, mul_inv_cancel_right]
  obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
    (subgroup_product_eq_subgroup_iff parent first second first_le second_le).mp whole element member.1
  obtain ⟨fixedFirst, fixedFirst_member, fixedSecond, fixedSecond_member, fixedProduct, first_fixed, second_fixed⟩ :=
    fixed_product_decomposition prime prime_prime actor actor_pgroup parent (first.subgroupOf parent)
      (second.subgroupOf parent) (normalized_subgroupOf_invariant actor parent first parent_normalized first_normalized)
      (normalized_subgroupOf_invariant actor parent second parent_normalized second_normalized)
      (coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card _)) internalElement fixed
      ⟨⟨firstElement, first_le first_member⟩, first_member, ⟨secondElement, second_le second_member⟩,
        second_member, Subtype.ext product⟩
  have first_central : fixedFirst.val ∈ Subgroup.centralizer (actor : Set GroupType) := by
    intro actorElement actor_member
    have equality := congrArg Subtype.val (first_fixed ⟨actorElement, actor_member⟩)
    change actorElement * fixedFirst.val * actorElement⁻¹ = fixedFirst.val at equality
    exact (mul_inv_eq_iff_eq_mul).mp equality
  have second_central : fixedSecond.val ∈ Subgroup.centralizer (actor : Set GroupType) := by
    intro actorElement actor_member
    have equality := congrArg Subtype.val (second_fixed ⟨actorElement, actor_member⟩)
    change actorElement * fixedSecond.val * actorElement⁻¹ = fixedSecond.val at equality
    exact (mul_inv_eq_iff_eq_mul).mp equality
  exact ⟨fixedFirst.val, ⟨fixedFirst_member, first_central⟩, fixedSecond.val, ⟨fixedSecond_member, second_central⟩,
    congrArg Subtype.val fixedProduct⟩

end CFSG.SignalizerFunctor.Helpers
