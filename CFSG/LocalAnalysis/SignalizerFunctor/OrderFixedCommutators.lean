module

public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableCommutingCommutators

public section

universe actorUniverse groupUniverse secondActorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [CommGroup ActorType]
variable {SecondActorType : Type secondActorUniverse} [Group SecondActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType] [MulDistribMulAction SecondActorType GroupType]

@[expose] def orderFixedActionCommutatorHull (prime rank : ℕ)
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) : Subgroup GroupType :=
  ⨆ actorSubgroup : Subgroup ActorType, ⨆ (_ : Nat.card actorSubgroup = prime ^ rank),
    invariantActionCommutator (FixedPoints.subgroup actorSubgroup GroupType)
      (commuting_fixed_subgroup_invariant commuting actorSubgroup)

theorem order_fixed_action_commutator_hull_le (prime rank : ℕ)
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    orderFixedActionCommutatorHull prime rank commuting ≤ actionCommutator (ActorType := SecondActorType) := by
  exact iSup_le fun _ => iSup_le fun _ => invariant_action_commutator_le_global _ _

theorem fixed_action_commutator_hull_le_order_hull [Finite ActorType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ (rank + 1) ≤ Nat.card ActorType)
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    fixedActionCommutatorHull commuting ≤ orderFixedActionCommutatorHull prime rank commuting := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have actor_pgroup : IsPGroup prime ActorType := by
    intro element
    exact ⟨1, by simpa using exponent element⟩
  apply iSup_le
  intro cyclicSubgroup
  apply iSup_le
  intro cyclic
  have index_bound := cyclic_quotient_index_le_prime prime prime_prime ActorType exponent cyclicSubgroup cyclic
  have subgroup_large : prime ^ rank ≤ Nat.card cyclicSubgroup := by
    have cardinality := cyclicSubgroup.card_mul_index
    have index_product := Nat.mul_le_mul_left (Nat.card cyclicSubgroup) index_bound
    rw [pow_succ] at large
    nlinarith [prime_prime.pos]
  obtain ⟨orderSubgroup, order_card⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card prime_prime
    (actor_pgroup.to_subgroup cyclicSubgroup) subgroup_large
  let embedded := orderSubgroup.map cyclicSubgroup.subtype
  have embedded_card : Nat.card embedded = prime ^ rank := by
    rw [Subgroup.card_map_of_injective cyclicSubgroup.subtype_injective]
    exact order_card
  apply le_trans _ (le_iSup_of_le embedded (le_iSup_of_le embedded_card le_rfl))
  apply invariant_action_commutator_mono
  intro element fixed actorElement
  obtain ⟨internal, _, mapped⟩ := actorElement.property
  have internal_fixed := fixed (⟨internal, internal.property⟩ : cyclicSubgroup)
  change actorElement.val • element = element
  rw [← mapped]
  exact internal_fixed

theorem solvable_order_fixed_action_commutator_hull [Finite ActorType] [Finite GroupType]
    [Group.IsSolvable GroupType]
    (prime rank actionPrime : ℕ) (prime_prime : prime.Prime) (action_prime : actionPrime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ (rank + 1) ≤ Nat.card ActorType)
    (second_pgroup : IsPGroup actionPrime SecondActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (second_coprime : Nat.Coprime actionPrime (Nat.card GroupType))
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    orderFixedActionCommutatorHull prime rank commuting = actionCommutator (ActorType := SecondActorType) := by
  have actor_pgroup : IsPGroup prime ActorType := by
    intro element
    exact ⟨1, by simpa using exponent element⟩
  apply le_antisymm (order_fixed_action_commutator_hull_le prime rank commuting)
  rw [← solvable_fixed_action_commutator_hull prime actionPrime prime_prime action_prime ActorType
    SecondActorType actor_pgroup second_pgroup GroupType coprime second_coprime commuting]
  exact fixed_action_commutator_hull_le_order_hull prime rank prime_prime exponent large commuting

theorem coprime_action_fixed_commutator_product [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime SecondActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) :
    subgroupProduct (FixedPoints.subgroup SecondActorType GroupType)
      (actionCommutator (ActorType := SecondActorType) (GroupType := GroupType)) = Set.univ := by
  let _normal := action_commutator_normal (ActorType := SecondActorType) (GroupType := GroupType)
  apply (subgroup_product_eq_univ_iff _ _).mpr
  intro element
  have factorization := coprime_action_commutator_factorization prime prime_prime actor_pgroup coprime
  rw [sup_comm] at factorization
  have member : element ∈ FixedPoints.subgroup SecondActorType GroupType ⊔
      actionCommutator (ActorType := SecondActorType) (GroupType := GroupType) := by
    rw [factorization]
    trivial
  exact Subgroup.mem_sup_of_normal_right.mp member

end CFSG.SignalizerFunctor.Helpers
