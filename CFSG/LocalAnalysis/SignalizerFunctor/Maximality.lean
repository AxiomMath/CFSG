module

public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryGeneration

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem elementary_abelian_centralizer_generation (prime rank : ℕ)
    (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (normalizes : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) :
    (⨆ subgroup ∈ signalizerFunctorEk prime rank actor,
      target ⊓ Subgroup.centralizer (subgroup : Set GroupType)) = target := by
  let := elementary.1
  let _actorCommGroup : CommGroup actor :=
    { actor.toGroup with mul_comm := mul_comm' }
  let _action := conjugationAction actor target normalizes
  have exponent : ∀ element : actor, element ^ prime = 1 := by
    intro element
    apply Subtype.ext
    exact elementary.2 element element.property
  have generated := elementary_abelian_order_generation prime rank prime_prime
    actor exponent large target coprime
  apply le_antisymm
  · apply iSup_le
    intro subgroup
    apply iSup_le
    intro _
    exact inf_le_left
  · have target_generated :
        (⨆ (internal : Subgroup actor) (_ : Nat.card internal = prime ^ rank),
          FixedPoints.subgroup internal target).map target.subtype = target := by
      rw [generated, ← MonoidHom.range_eq_map, target.subtype_range]
    conv_lhs => rw [← target_generated]
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro internal
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro internal_card
    let embedded := internal.map actor.subtype
    have embedded_le : embedded ≤ actor := by
      rintro element ⟨representative, _, rfl⟩
      exact representative.property
    have embedded_card : Nat.card embedded = prime ^ rank := by
      rw [Subgroup.card_map_of_injective actor.subtype_injective]
      exact internal_card
    have embedded_member : embedded ∈ signalizerFunctorEk prime rank actor :=
      ⟨embedded_le, embedded_card⟩
    apply le_trans _ (le_iSup_of_le embedded (le_iSup_of_le embedded_member le_rfl))
    rintro element ⟨representative, fixed, rfl⟩
    refine ⟨representative.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro actorElement member
    obtain ⟨internalElement, internal_member, rfl⟩ := member
    have equality := congrArg (fun internalTarget : target => (internalTarget : GroupType))
      (fixed (⟨internalElement, internal_member⟩ : internal))
    change internalElement.val * representative.val * internalElement.val⁻¹ =
      representative.val at equality
    exact mul_inv_eq_iff_eq_mul.mp equality

theorem signalizer_maximality (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (values_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (target : Subgroup GroupType)
    (normalizes : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (fixed_contained : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      target ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) :
    target ≤ ⨆ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    have bound : prime ^ rank ≤ prime ^ (rank + 1) := by
      rw [pow_succ]
      calc
        prime ^ rank = prime ^ rank * 1 := (mul_one _).symm
        _ ≤ prime ^ rank * prime := Nat.mul_le_mul_left _ (by
          have := prime_prime.two_le
          omega)
    exact bound.trans large
  have coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    rank_large values values_coprime target normalizes fixed_contained
  rw [← elementary_abelian_centralizer_generation prime rank prime_prime actor target
    elementary large normalizes coprime]
  apply iSup_le
  intro subgroup
  apply iSup_le
  intro member
  exact (fixed_contained subgroup member).trans
    (le_iSup_of_le subgroup (le_iSup_of_le member le_rfl))

end CFSG.SignalizerFunctor.Helpers
