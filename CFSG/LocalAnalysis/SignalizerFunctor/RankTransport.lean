module

public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem cardinality_sup_of_disjoint_commutative
    {GroupType : Type groupUniverse} [CommGroup GroupType]
    (first second : Subgroup GroupType) (disjoint : Disjoint first second) :
    Nat.card (first ⊔ second : Subgroup GroupType) = Nat.card first * Nat.card second := by
  let combined : Subgroup GroupType := first ⊔ second
  let firstInternal := first.subgroupOf combined
  let secondInternal := second.subgroupOf combined
  have internal_disjoint : Disjoint firstInternal secondInternal := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro element member
    change element = 1
    apply Subtype.ext
    have ambient_member : element.val ∈ first ⊓ second := member
    rw [disjoint.eq_bot] at ambient_member
    exact ambient_member
  have internal_whole : firstInternal ⊔ secondInternal = ⊤ := by
    apply top_unique
    intro element _
    obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
      Subgroup.mem_sup.mp element.property
    apply Subgroup.mem_sup.mpr
    refine ⟨⟨firstElement, Subgroup.mem_sup_left first_member⟩, first_member,
      ⟨secondElement, Subgroup.mem_sup_right second_member⟩, second_member, ?_⟩
    exact Subtype.ext product
  have complementary : IsCompl firstInternal secondInternal :=
    ⟨internal_disjoint, codisjoint_iff.mpr internal_whole⟩
  have cardinality := (isComplement'_of_isCompl_commutative complementary).card_mul_card
  have first_card : Nat.card firstInternal = Nat.card first :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show first ≤ combined from le_sup_left)).toEquiv
  have second_card : Nat.card secondInternal = Nat.card second :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show second ≤ combined from le_sup_right)).toEquiv
  rw [first_card, second_card] at cardinality
  exact cardinality.symm

theorem complement_rank_bound
    {GroupType : Type groupUniverse} [Group GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (subgroup complement : Subgroup GroupType)
    (complementary : subgroup.IsComplement' complement)
    (subgroup_card : Nat.card subgroup = prime ^ rank)
    (large : prime ^ (rank + 3) ≤ Nat.card GroupType) :
    prime ^ 3 ≤ Nat.card complement := by
  have cardinality := complementary.card_mul_card
  rw [subgroup_card] at cardinality
  rw [pow_add, ← cardinality] at large
  exact Nat.le_of_mul_le_mul_left large (pow_pos prime_prime.pos rank)

theorem subgroup_decomposition_along_complement
    {GroupType : Type groupUniverse} [CommGroup GroupType]
    (first second target : Subgroup GroupType)
    (complementary : first.IsComplement' second) (first_le : first ≤ target) :
    target = first ⊔ (target ⊓ second) := by
  apply le_antisymm
  · intro element member
    have decomposable : element ∈ first ⊔ second := by
      rw [complementary.sup_eq_top]
      trivial
    obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
      Subgroup.mem_sup.mp decomposable
    have second_in_target : secondElement ∈ target := by
      have product_member : firstElement * secondElement ∈ target := by
        rw [product]
        exact member
      have cancelled := target.mul_mem (target.inv_mem (first_le first_member)) product_member
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using cancelled
    exact Subgroup.mem_sup.mpr
      ⟨firstElement, first_member, secondElement, ⟨second_in_target, second_member⟩, product⟩
  · exact sup_le first_le inf_le_left

theorem rank_one_subgroup_transport
    {GroupType : Type groupUniverse} [CommGroup GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (first second : Subgroup GroupType) (complementary : first.IsComplement' second)
    (first_card : Nat.card first = prime ^ rank)
    (target : Subgroup GroupType) (first_le : first ≤ target)
    (target_card : Nat.card target = prime ^ (rank + 1)) :
    target = first ⊔ (target ⊓ second) ∧ Nat.card (target ⊓ second : Subgroup GroupType) = prime := by
  have decomposition := subgroup_decomposition_along_complement first second target
    complementary first_le
  refine ⟨decomposition, ?_⟩
  have disjoint : Disjoint first (target ⊓ second) :=
    complementary.disjoint.mono_right inf_le_right
  have cardinality := cardinality_sup_of_disjoint_commutative first (target ⊓ second) disjoint
  rw [← decomposition, target_card, first_card, pow_succ] at cardinality
  exact Nat.eq_of_mul_eq_mul_left (pow_pos prime_prime.pos rank) cardinality.symm

theorem sup_inf_eq_of_disjoint_commutative
    {GroupType : Type groupUniverse} [CommGroup GroupType]
    (first second rest : Subgroup GroupType) (disjoint : Disjoint first second)
    (rest_le : rest ≤ second) : (first ⊔ rest) ⊓ second = rest := by
  apply le_antisymm
  · rintro element ⟨product_member, second_member⟩
    obtain ⟨firstElement, first_member, restElement, rest_member, product⟩ :=
      Subgroup.mem_sup.mp product_member
    have first_in_second : firstElement ∈ second := by
      have product_in_second : firstElement * restElement ∈ second := by
        rw [product]
        exact second_member
      have cancelled := second.mul_mem product_in_second (second.inv_mem (rest_le rest_member))
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using cancelled
    have first_one : firstElement = 1 := by
      have both_member : firstElement ∈ first ⊓ second := ⟨first_member, first_in_second⟩
      rw [disjoint.eq_bot] at both_member
      exact both_member
    rw [first_one, one_mul] at product
    rw [← product]
    exact rest_member
  · exact le_inf le_sup_right rest_le

noncomputable def complement_order_subgroup_equiv
    {GroupType : Type groupUniverse} [CommGroup GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (first second : Subgroup GroupType) (complementary : first.IsComplement' second)
    (first_card : Nat.card first = prime ^ rank) :
    {internal : Subgroup second // Nat.card internal = prime} ≃
      {target : Subgroup GroupType // first ≤ target ∧ Nat.card target = prime ^ (rank + 1)} where
  toFun internal := ⟨first ⊔ internal.val.map second.subtype, le_sup_left, by
    have disjoint : Disjoint first (internal.val.map second.subtype) :=
      complementary.disjoint.mono_right (Subgroup.map_subtype_le internal.val)
    rw [cardinality_sup_of_disjoint_commutative first (internal.val.map second.subtype)
      disjoint, first_card, Subgroup.card_map_of_injective second.subtype_injective,
      internal.property, pow_succ]⟩
  invFun target := ⟨target.val.subgroupOf second, by
    have intersection_card := (rank_one_subgroup_transport prime rank prime_prime first second
      complementary first_card target.val target.property.1 target.property.2).2
    have mapped_card := Subgroup.card_map_of_injective
      (K := target.val.subgroupOf second) second.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype] at mapped_card
    exact mapped_card.symm.trans intersection_card⟩
  left_inv internal := by
    apply Subtype.ext
    apply Subgroup.map_injective second.subtype_injective
    change ((first ⊔ internal.val.map second.subtype).subgroupOf second).map second.subtype =
      internal.val.map second.subtype
    rw [Subgroup.subgroupOf_map_subtype,
      sup_inf_eq_of_disjoint_commutative first second (internal.val.map second.subtype)
        complementary.disjoint (Subgroup.map_subtype_le internal.val)]
  right_inv target := by
    apply Subtype.ext
    change first ⊔ (target.val.subgroupOf second).map second.subtype = target.val
    rw [Subgroup.subgroupOf_map_subtype]
    exact (subgroup_decomposition_along_complement first second target.val complementary
      target.property.1).symm

end CFSG.SignalizerFunctor.Helpers
