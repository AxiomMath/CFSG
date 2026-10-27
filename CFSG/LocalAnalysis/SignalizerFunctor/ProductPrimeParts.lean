module

public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

theorem prime_parts_mul_eq_of_mul_eq (prime first second third fourth : ℕ)
    (first_nonzero : first ≠ 0) (second_nonzero : second ≠ 0)
    (third_nonzero : third ≠ 0) (fourth_nonzero : fourth ≠ 0)
    (equal : first * second = third * fourth) :
    prime ^ first.factorization prime * prime ^ second.factorization prime =
      prime ^ third.factorization prime * prime ^ fourth.factorization prime := by
  have factor_eq := congrArg (fun cardinality : ℕ => cardinality.factorization prime) equal
  rw [Nat.factorization_mul first_nonzero second_nonzero,
    Nat.factorization_mul third_nonzero fourth_nonzero, Finsupp.add_apply, Finsupp.add_apply] at factor_eq
  rw [← pow_add, factor_eq, pow_add]

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem subgroup_product_eq_subgroup_iff (parent first second : Subgroup GroupType)
    (first_le : first ≤ parent) (second_le : second ≤ parent) :
    subgroupProduct first second = (parent : Set GroupType) ↔
      ∀ element ∈ parent, ∃ firstElement ∈ first, ∃ secondElement ∈ second,
        firstElement * secondElement = element := by
  constructor
  · intro product_eq element member
    have product_member : element ∈ subgroupProduct first second := by rw [product_eq]; exact member
    exact product_member
  · intro decomposable
    ext element
    constructor
    · rintro ⟨firstElement, first_member, secondElement, second_member, rfl⟩
      exact parent.mul_mem (first_le first_member) (second_le second_member)
    · exact decomposable element

omit [Finite GroupType] in
theorem subgroup_product_cardinality_of_subgroup_whole
    (parent first second : Subgroup GroupType) (first_le : first ≤ parent) (second_le : second ≤ parent)
    (whole : ∀ element ∈ parent, ∃ firstElement ∈ first, ∃ secondElement ∈ second,
      firstElement * secondElement = element) :
    Nat.card first * Nat.card second = Nat.card parent * Nat.card (first ⊓ second : Subgroup GroupType) := by
  have product_eq := (subgroup_product_eq_subgroup_iff parent first second first_le second_le).mpr whole
  have cardinality := subgroup_product_cardinality first second
  rw [product_eq] at cardinality
  exact cardinality

theorem subgroup_product_eq_of_card_formula (parent first second : Subgroup GroupType)
    (first_le : first ≤ parent) (second_le : second ≤ parent)
    (formula : Nat.card first * Nat.card second =
      Nat.card parent * Nat.card (first ⊓ second : Subgroup GroupType)) :
    subgroupProduct first second = (parent : Set GroupType) := by
  have product_card : Nat.card (subgroupProduct first second) = Nat.card parent := by
    have cardinality := subgroup_product_cardinality first second
    rw [formula] at cardinality
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (first ⊓ second : Subgroup GroupType))) cardinality.symm
  have contained : subgroupProduct first second ⊆ (parent : Set GroupType) := by
    rintro element ⟨firstElement, first_member, secondElement, second_member, rfl⟩
    exact parent.mul_mem (first_le first_member) (second_le second_member)
  let _firstFintype := Fintype.ofFinite (subgroupProduct first second)
  let _parentFintype := Fintype.ofFinite parent
  apply Set.eq_of_subset_of_card_le contained
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  change Nat.card parent ≤ Nat.card (subgroupProduct first second)
  exact product_card.symm.le

omit [Finite GroupType] in
theorem subgroup_product_cardinality_of_whole (first second : Subgroup GroupType)
    (whole : ∀ element : GroupType, ∃ firstElement ∈ first, ∃ secondElement ∈ second,
      firstElement * secondElement = element) :
    Nat.card first * Nat.card second = Nat.card GroupType * Nat.card (first ⊓ second : Subgroup GroupType) := by
  have product_eq := (subgroup_product_eq_univ_iff first second).mpr whole
  have cardinality := subgroup_product_cardinality first second
  rw [product_eq, Nat.card_univ] at cardinality
  exact cardinality

theorem subgroup_product_card_eq_subgroup_of_sylow_parts
    (prime : ℕ) (prime_prime : prime.Prime)
    (parent first second : Subgroup GroupType) (first_le : first ≤ parent) (second_le : second ≤ parent)
    (ambientParent ambientFirst ambientSecond : Subgroup GroupType)
    (parentSylow : Sylow prime ambientParent) (firstSylow : Sylow prime ambientFirst)
    (secondSylow : Sylow prime ambientSecond)
    (intersectionSylow : Sylow prime (ambientFirst ⊓ ambientSecond : Subgroup GroupType))
    (parent_card : Nat.card parent = Nat.card (parentSylow : Subgroup ambientParent))
    (first_card : Nat.card first = Nat.card (firstSylow : Subgroup ambientFirst))
    (second_card : Nat.card second = Nat.card (secondSylow : Subgroup ambientSecond))
    (intersection_card : Nat.card (first ⊓ second : Subgroup GroupType) =
      Nat.card (intersectionSylow : Subgroup (ambientFirst ⊓ ambientSecond : Subgroup GroupType)))
    (ambient_card : Nat.card ambientFirst * Nat.card ambientSecond =
      Nat.card ambientParent * Nat.card (ambientFirst ⊓ ambientSecond : Subgroup GroupType)) :
    subgroupProduct first second = (parent : Set GroupType) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have part_eq := prime_parts_mul_eq_of_mul_eq prime (Nat.card ambientFirst) (Nat.card ambientSecond)
    (Nat.card ambientParent) (Nat.card (ambientFirst ⊓ ambientSecond : Subgroup GroupType))
    (Nat.card_pos.ne') (Nat.card_pos.ne') (Nat.card_pos.ne') (Nat.card_pos.ne') ambient_card
  have sylow_formula : Nat.card first * Nat.card second =
      Nat.card parent * Nat.card (first ⊓ second : Subgroup GroupType) := by
    rw [parent_card, first_card, second_card, intersection_card, parentSylow.card_eq_multiplicity,
      firstSylow.card_eq_multiplicity, secondSylow.card_eq_multiplicity,
      intersectionSylow.card_eq_multiplicity]
    exact part_eq
  have product_card : Nat.card (subgroupProduct first second) = Nat.card parent := by
    have cardinality := subgroup_product_cardinality first second
    rw [sylow_formula] at cardinality
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (first ⊓ second : Subgroup GroupType))) cardinality.symm
  have contained : subgroupProduct first second ⊆ (parent : Set GroupType) := by
    rintro element ⟨firstElement, first_member, secondElement, second_member, rfl⟩
    exact parent.mul_mem (first_le first_member) (second_le second_member)
  let _firstFintype := Fintype.ofFinite (subgroupProduct first second)
  let _parentFintype := Fintype.ofFinite parent
  apply Set.eq_of_subset_of_card_le contained
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  change Nat.card parent ≤ Nat.card (subgroupProduct first second)
  exact product_card.symm.le

end CFSG.SignalizerFunctor.Helpers
