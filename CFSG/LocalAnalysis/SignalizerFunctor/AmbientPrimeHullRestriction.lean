module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSubfunctorValues
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeHullRestriction
public import CFSG.LocalAnalysis.SignalizerFunctor.FixedHullEquiv

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem ambient_fixed_normalized_prime_hull_restriction
    (prime : ℕ) (prime_prime : prime.Prime) (actor larger smaller : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor) (contained : smaller ≤ larger)
    (larger_normalized : actor ≤ Subgroup.normalizer (larger : Set GroupType))
    (smaller_normalized : actor ≤ Subgroup.normalizer (smaller : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card larger)) (solvable : Group.IsSolvable larger)
    (fixed_normalized : larger ⊓ Subgroup.centralizer (actor : Set GroupType) ≤
      Subgroup.normalizer (smaller : Set GroupType)) (primes : Set ℕ) :
    let _largerAction := conjugationAction actor larger larger_normalized
    let _smallerAction := conjugationAction actor smaller smaller_normalized
    (fixedNormalizedPrimeHull (ActorType := actor) (GroupType := smaller) primes).map smaller.subtype =
      (fixedNormalizedPrimeHull (ActorType := actor) (GroupType := larger) primes).map larger.subtype ⊓
        smaller := by
  let := solvable
  let _largerAction := conjugationAction actor larger larger_normalized
  let _smallerAction := conjugationAction actor smaller smaller_normalized
  let internal := smaller.subgroupOf larger
  have internal_invariant := normalized_subgroupOf_invariant actor larger smaller larger_normalized
    smaller_normalized
  let _internalAction := invariantSubgroupAction internal internal_invariant
  have internal_fixed_normalized := normalized_subgroupOf_fixed_normalized actor larger smaller
    (larger ⊓ Subgroup.centralizer (actor : Set GroupType)) larger_normalized le_rfl fixed_normalized
  have restricted_hull := fixed_normalized_prime_hull_restriction prime prime_prime actor_pgroup
    coprime primes internal internal_invariant internal_fixed_normalized
  let equivalence : internal ≃* smaller := Subgroup.subgroupOfEquivOfLe contained
  have equivariant : ∀ actorElement : actor, ∀ element : internal,
      equivalence (actorElement • element) = actorElement • equivalence element := by
    intro actorElement element
    apply Subtype.ext
    rfl
  have transported_hull := fixed_normalized_prime_hull_map_equiv primes equivalence equivariant
  have composite : smaller.subtype.comp equivalence.toMonoidHom =
      larger.subtype.comp internal.subtype := by
    ext element
    rfl
  change (fixedNormalizedPrimeHull (ActorType := actor) (GroupType := smaller) primes).map
    smaller.subtype = _
  rw [← transported_hull, Subgroup.map_map, composite, ← Subgroup.map_map, restricted_hull,
    Subgroup.map_inf _ _ larger.subtype larger.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le contained]

end CFSG.SignalizerFunctor.Helpers
