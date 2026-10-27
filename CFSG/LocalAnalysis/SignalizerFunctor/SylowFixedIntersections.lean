module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowIntersections

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem invariant_sylow_fixed_intersection
    {ActorType : Type actorUniverse} [Group ActorType]
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    [MulDistribMulAction ActorType GroupType]
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor_pgroup : IsPGroup prime ActorType) (coprime : Nat.Coprime prime (Nat.card GroupType))
    (sylow : Sylow groupPrime GroupType) (fixed : ∀ actorElement : ActorType, actorElement • sylow = sylow) :
    ∃ fixedSylow : Sylow groupPrime (FixedPoints.subgroup ActorType GroupType),
      (fixedSylow : Subgroup (FixedPoints.subgroup ActorType GroupType)).map
        (FixedPoints.subgroup ActorType GroupType).subtype =
          (sylow : Subgroup GroupType) ⊓ FixedPoints.subgroup ActorType GroupType := by
  have invariant : ∀ actorElement : ActorType, ∀ element ∈ FixedPoints.subgroup ActorType GroupType,
      actorElement • element ∈ FixedPoints.subgroup ActorType GroupType := by
    intro actorElement element member
    rw [member actorElement]
    exact member
  obtain ⟨fixedSylow, equal, _⟩ := fixed_normalized_invariant_sylow_intersection prime groupPrime
    prime_prime groupPrime_prime actor_pgroup coprime sylow fixed (FixedPoints.subgroup ActorType GroupType)
    invariant Subgroup.le_normalizer
  exact ⟨fixedSylow, equal⟩

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem normalized_sylow_centralizer_intersection
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor parent : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card parent)) (sylow : Sylow groupPrime parent)
    (sylow_normalized : actor ≤ Subgroup.normalizer
      (((sylow : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType)) :
    ∃ fixedSylow : Sylow groupPrime (parent ⊓ Subgroup.centralizer (actor : Set GroupType) : Subgroup GroupType),
      (fixedSylow : Subgroup (parent ⊓ Subgroup.centralizer (actor : Set GroupType) : Subgroup GroupType)).map
        (parent ⊓ Subgroup.centralizer (actor : Set GroupType)).subtype =
          (sylow : Subgroup parent).map parent.subtype ⊓ Subgroup.centralizer (actor : Set GroupType) := by
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  let _action := conjugationAction actor parent normalized
  have fixed := invariant_subgroup_sylow_fixed actor parent normalized groupPrime sylow sylow_normalized
  obtain ⟨internalSylow, internal_eq⟩ := invariant_sylow_fixed_intersection prime groupPrime prime_prime
    groupPrime_prime actor_pgroup coprime sylow fixed
  let fixedSubgroup := FixedPoints.subgroup actor parent
  let ambientFixed := parent ⊓ Subgroup.centralizer (actor : Set GroupType)
  have fixed_eq : fixedSubgroup.map parent.subtype = ambientFixed :=
    conjugation_fixed_subgroup_map actor parent normalized
  let equivalence : fixedSubgroup ≃* ambientFixed :=
    (fixedSubgroup.equivMapOfInjective parent.subtype parent.subtype_injective).trans
      (MulEquiv.subgroupCongr fixed_eq)
  have surjective : Function.Surjective equivalence.toMonoidHom := equivalence.surjective
  let fixedSylow := internalSylow.mapSurjective (f := equivalence.toMonoidHom) surjective
  refine ⟨fixedSylow, ?_⟩
  change (internalSylow.mapSurjective (f := equivalence.toMonoidHom) surjective : Subgroup ambientFixed).map
    ambientFixed.subtype = _
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hom_eq : ambientFixed.subtype.comp equivalence.toMonoidHom = parent.subtype.comp fixedSubgroup.subtype := by
    ext element
    rfl
  rw [hom_eq, ← Subgroup.map_map, internal_eq,
    Subgroup.map_inf _ _ _ parent.subtype_injective, fixed_eq]
  rw [← inf_assoc, inf_eq_left.mpr (Subgroup.map_subtype_le _)]

end CFSG.SignalizerFunctor.Helpers
