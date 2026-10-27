module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimePowerFixedFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.ProductPrimeParts
public import CFSG.LocalAnalysis.SignalizerFunctor.SylowIntersectionPrimeParts

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [CommGroup ActorType] [Finite ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable [MulDistribMulAction ActorType GroupType]

omit [Finite ActorType] in
theorem sylow_local_order_fixed_product
    (prime rank groupPrime : ℕ)
    (first second : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first, actorElement • element ∈ first)
    (first_normalized : FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer (first : Set GroupType))
    (sylow : Sylow groupPrime GroupType)
    (parts : ∀ subgroup : Subgroup GroupType,
      (∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup) →
      FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer (subgroup : Set GroupType) →
      Nat.card ((sylow : Subgroup GroupType) ⊓ subgroup : Subgroup GroupType) =
        groupPrime ^ (Nat.card subgroup).factorization groupPrime ∧
      Nat.card (((sylow : Subgroup GroupType) ⊓ second) ⊓ subgroup : Subgroup GroupType) =
        groupPrime ^ (Nat.card (second ⊓ subgroup : Subgroup GroupType)).factorization groupPrime)
    (local_factorization : ∀ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ^ rank →
      ∀ element ∈ FixedPoints.subgroup actorSubgroup GroupType,
        ∃ firstElement ∈ first ⊓ FixedPoints.subgroup actorSubgroup GroupType,
          ∃ secondElement ∈ second ⊓ FixedPoints.subgroup actorSubgroup GroupType,
            firstElement * secondElement = element)
    (actorSubgroup : Subgroup ActorType) (actorSubgroup_card : Nat.card actorSubgroup = prime ^ rank) :
    subgroupProduct
        (((sylow : Subgroup GroupType) ⊓ first) ⊓ FixedPoints.subgroup actorSubgroup GroupType)
        (((sylow : Subgroup GroupType) ⊓ second) ⊓ FixedPoints.subgroup actorSubgroup GroupType) =
      ((sylow : Subgroup GroupType) ⊓ FixedPoints.subgroup actorSubgroup GroupType : Set GroupType) := by
  let fixed := FixedPoints.subgroup actorSubgroup GroupType
  let firstFixed := first ⊓ fixed
  let secondFixed := second ⊓ fixed
  have fixed_invariant := fixed_subgroup_invariant_of_commutative_actor
    (GroupType := GroupType) actorSubgroup
  have fixed_normalized := full_fixed_normalizes_subgroup_fixed (GroupType := GroupType) actorSubgroup
  have first_fixed_invariant := invariant_inf_subgroups first fixed first_invariant fixed_invariant
  have first_fixed_normalized := normalizer_inf_of_le (FixedPoints.subgroup ActorType GroupType)
    first fixed first_normalized fixed_normalized
  have fixed_parts := parts fixed fixed_invariant fixed_normalized
  have first_parts := parts firstFixed first_fixed_invariant first_fixed_normalized
  have ambient_formula := subgroup_product_cardinality_of_subgroup_whole fixed firstFixed secondFixed
    inf_le_right inf_le_right (local_factorization actorSubgroup actorSubgroup_card)
  have prime_formula := prime_parts_mul_eq_of_mul_eq groupPrime (Nat.card firstFixed) (Nat.card secondFixed)
    (Nat.card fixed) (Nat.card (firstFixed ⊓ secondFixed : Subgroup GroupType))
    Nat.card_pos.ne' Nat.card_pos.ne' Nat.card_pos.ne' Nat.card_pos.ne' ambient_formula
  have first_card : Nat.card (((sylow : Subgroup GroupType) ⊓ first) ⊓ fixed : Subgroup GroupType) =
      groupPrime ^ (Nat.card firstFixed).factorization groupPrime := by
    rw [inf_assoc]
    exact first_parts.1
  have second_card := fixed_parts.2
  have intersection_eq :
      ((((sylow : Subgroup GroupType) ⊓ first) ⊓ fixed) ⊓
        (((sylow : Subgroup GroupType) ⊓ second) ⊓ fixed)) =
          ((sylow : Subgroup GroupType) ⊓ second) ⊓ firstFixed := by
    ext element
    constructor
    · exact fun member => ⟨⟨member.1.1.1, member.2.1.2⟩, member.1.1.2, member.1.2⟩
    · exact fun member => ⟨⟨⟨member.1.1, member.2.1⟩, member.2.2⟩, ⟨member.1, member.2.2⟩⟩
  have ambient_intersection_eq : firstFixed ⊓ secondFixed = second ⊓ firstFixed := by
    ext element
    constructor
    · exact fun member => ⟨member.2.1, member.1⟩
    · exact fun member => ⟨member.2, member.1, member.2.2⟩
  have formula :
      Nat.card (((sylow : Subgroup GroupType) ⊓ first) ⊓ fixed : Subgroup GroupType) *
        Nat.card (((sylow : Subgroup GroupType) ⊓ second) ⊓ fixed : Subgroup GroupType) =
          Nat.card ((sylow : Subgroup GroupType) ⊓ fixed : Subgroup GroupType) *
            Nat.card (((((sylow : Subgroup GroupType) ⊓ first) ⊓ fixed) ⊓
              (((sylow : Subgroup GroupType) ⊓ second) ⊓ fixed)) : Subgroup GroupType) := by
    rw [first_card, second_card, fixed_parts.1, intersection_eq, first_parts.2]
    rwa [ambient_intersection_eq] at prime_formula
  exact subgroup_product_eq_of_card_formula _ _ _
    (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_left) formula

theorem coprime_sylow_order_fixed_factorization
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime_prime : groupPrime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ (rank + 1) ≤ Nat.card ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (first second : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first, actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second, actorElement • element ∈ second)
    (first_normalized : FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer (first : Set GroupType))
    (local_factorization : ∀ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ^ rank →
      ∀ element ∈ FixedPoints.subgroup actorSubgroup GroupType,
        ∃ firstElement ∈ first ⊓ FixedPoints.subgroup actorSubgroup GroupType,
          ∃ secondElement ∈ second ⊓ FixedPoints.subgroup actorSubgroup GroupType,
            firstElement * secondElement = element) :
    ∃ sylow : Sylow groupPrime GroupType,
      Nat.card ((sylow : Subgroup GroupType) ⊓ first : Subgroup GroupType) =
        groupPrime ^ (Nat.card first).factorization groupPrime ∧
      Nat.card ((sylow : Subgroup GroupType) ⊓ second : Subgroup GroupType) =
        groupPrime ^ (Nat.card second).factorization groupPrime ∧
      Nat.card (((sylow : Subgroup GroupType) ⊓ first) ⊓ second : Subgroup GroupType) =
        groupPrime ^ (Nat.card (first ⊓ second : Subgroup GroupType)).factorization groupPrime ∧
      subgroupProduct ((sylow : Subgroup GroupType) ⊓ first) ((sylow : Subgroup GroupType) ⊓ second) =
        ((sylow : Subgroup GroupType) : Set GroupType) := by
  have actor_pgroup : IsPGroup prime ActorType := by
    intro element
    exact ⟨1, by simpa only [pow_one] using exponent element⟩
  obtain ⟨sylow, fixed, second_card, parts⟩ := invariant_sylow_with_supplement_intersection_parts
    prime groupPrime prime_prime groupPrime_prime_prime actor_pgroup coprime second second_invariant
  have first_parts := parts first first_invariant first_normalized
  have intersection_eq : ((sylow : Subgroup GroupType) ⊓ first) ⊓ second =
      ((sylow : Subgroup GroupType) ⊓ second) ⊓ first := by
    rw [inf_assoc, inf_comm first second, ← inf_assoc]
  refine ⟨sylow, first_parts.1, second_card, ?_, ?_⟩
  · rw [intersection_eq, inf_comm first second]
    exact first_parts.2
  · let parent : Subgroup GroupType := sylow
    have parent_invariant := (invariant_sylow_subgroup_iff groupPrime sylow).mp fixed
    let _parentAction := invariantSubgroupAction parent parent_invariant
    have left_invariant : ∀ actorElement : ActorType, ∀ element ∈ first.subgroupOf parent,
        actorElement • element ∈ first.subgroupOf parent := by
      intro actorElement element member
      exact first_invariant actorElement element.val member
    have right_invariant : ∀ actorElement : ActorType, ∀ element ∈ second.subgroupOf parent,
        actorElement • element ∈ second.subgroupOf parent := by
      intro actorElement element member
      exact second_invariant actorElement element.val member
    have left_normalized : FixedPoints.subgroup ActorType parent ≤
        Subgroup.normalizer (first.subgroupOf parent : Set parent) := by
      apply Subgroup.le_normalizer_iff.mpr
      intro conjugator fixed element member
      have ambient_fixed : conjugator.val ∈ FixedPoints.subgroup ActorType GroupType := by
        intro actorElement
        exact congrArg Subtype.val (fixed actorElement)
      exact Subgroup.le_normalizer_iff.mp first_normalized conjugator.val ambient_fixed element.val member
    have local_parent : ∀ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ^ rank →
        ∀ element ∈ FixedPoints.subgroup actorSubgroup parent,
          ∃ leftElement ∈ first.subgroupOf parent ⊓ FixedPoints.subgroup actorSubgroup parent,
            ∃ rightElement ∈ second.subgroupOf parent ⊓ FixedPoints.subgroup actorSubgroup parent,
              leftElement * rightElement = element := by
      intro actorSubgroup actorSubgroup_card element element_fixed
      have ambient_fixed : element.val ∈ FixedPoints.subgroup actorSubgroup GroupType := by
        intro actorElement
        exact congrArg Subtype.val (element_fixed actorElement)
      have product_eq := sylow_local_order_fixed_product prime rank groupPrime first second
        first_invariant first_normalized sylow parts local_factorization actorSubgroup actorSubgroup_card
      have member : element.val ∈ subgroupProduct
          (((sylow : Subgroup GroupType) ⊓ first) ⊓ FixedPoints.subgroup actorSubgroup GroupType)
          (((sylow : Subgroup GroupType) ⊓ second) ⊓ FixedPoints.subgroup actorSubgroup GroupType) := by
        rw [product_eq]
        exact ⟨element.property, ambient_fixed⟩
      obtain ⟨leftElement, left_member, rightElement, right_member, product⟩ := member
      refine ⟨⟨leftElement, left_member.1.1⟩, ⟨left_member.1.2, ?_⟩,
        ⟨rightElement, right_member.1.1⟩, ⟨right_member.1.2, ?_⟩, Subtype.ext product⟩
      · intro actorElement
        exact Subtype.ext (left_member.2 actorElement)
      · intro actorElement
        exact Subtype.ext (right_member.2 actorElement)
    have parent_coprime := coprime.of_dvd_right parent.card_subgroup_dvd_card
    have parent_factorization := prime_power_order_fixed_factorization prime rank groupPrime prime_prime groupPrime_prime_prime
      exponent large parent_coprime sylow.isPGroup' (first.subgroupOf parent) (second.subgroupOf parent)
      left_invariant right_invariant left_normalized local_parent
    apply (subgroup_product_eq_subgroup_iff parent _ _ inf_le_left inf_le_left).mpr
    intro element member
    obtain ⟨leftElement, left_member, rightElement, right_member, product⟩ :=
      parent_factorization ⟨element, member⟩
    exact ⟨leftElement.val, ⟨leftElement.property, left_member⟩,
      rightElement.val, ⟨rightElement.property, right_member⟩, congrArg Subtype.val product⟩

end CFSG.SignalizerFunctor.Helpers
