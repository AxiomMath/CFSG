module

public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeGeneration

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem cyclic_quotient_index_le_prime
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [CommGroup ActorType]
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (subgroup : Subgroup ActorType) (cyclic : IsCyclic (ActorType ⧸ subgroup)) :
    subgroup.index ≤ prime := by
  let := cyclic
  have quotient_exponent : ∀ element : ActorType ⧸ subgroup, element ^ prime = 1 := by
    intro element
    induction element using QuotientGroup.induction_on with
    | H representative =>
      change QuotientGroup.mk' subgroup representative ^ prime = 1
      rw [← map_pow, exponent, map_one]
  have divides : Nat.card (ActorType ⧸ subgroup) ∣ prime := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr quotient_exponent
  rw [subgroup.index_eq_card]
  exact Nat.le_of_dvd prime_prime.pos divides

theorem elementary_abelian_order_generation
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ (rank + 1) ≤ Nat.card ActorType)
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType)) :
    (⨆ (actorSubgroup : Subgroup ActorType) (_ : Nat.card actorSubgroup = prime ^ rank),
      FixedPoints.subgroup actorSubgroup GroupType) = ⊤ := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have actor_pgroup : IsPGroup prime ActorType := by
    intro element
    exact ⟨1, by simpa using exponent element⟩
  apply top_unique
  rw [← coprime_cyclic_quotient_generation prime prime_prime ActorType actor_pgroup
    GroupType coprime]
  apply iSup_le
  intro cyclicSubgroup
  apply iSup_le
  intro cyclic
  have index_bound := cyclic_quotient_index_le_prime prime prime_prime ActorType exponent
    cyclicSubgroup cyclic
  have subgroup_large : prime ^ rank ≤ Nat.card cyclicSubgroup := by
    have cardinality := cyclicSubgroup.card_mul_index
    have index_product := Nat.mul_le_mul_left (Nat.card cyclicSubgroup) index_bound
    rw [pow_succ] at large
    nlinarith [prime_prime.pos]
  obtain ⟨orderSubgroup, order_card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card prime_prime
      (actor_pgroup.to_subgroup cyclicSubgroup) subgroup_large
  let embedded := orderSubgroup.map cyclicSubgroup.subtype
  have embedded_card : Nat.card embedded = prime ^ rank := by
    rw [Subgroup.card_map_of_injective cyclicSubgroup.subtype_injective]
    exact order_card
  apply le_trans _ (le_iSup_of_le embedded (le_iSup_of_le embedded_card le_rfl))
  intro element fixed actorElement
  obtain ⟨internal, _, mapped⟩ := actorElement.property
  have internal_fixed := fixed (⟨internal, internal.property⟩ : cyclicSubgroup)
  change (actorElement.val : ActorType) • element = element
  rw [← mapped]
  exact internal_fixed

end CFSG.SignalizerFunctor.Helpers
