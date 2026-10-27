module

public import CFSG.LocalAnalysis.SignalizerFunctor.SemidirectHall
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantHallConjugacy

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType]

@[expose] def fixedNormalizedPrimeHull (primes : Set ℕ) : Subgroup GroupType :=
  ⨆ (subgroup : Subgroup GroupType)
    (_ : primeSupported primes (Nat.card subgroup) ∧
      (∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup) ∧
      FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer (subgroup : Set GroupType)),
    subgroup

theorem fixed_normalized_prime_subgroup_le_invariant_hall
    [Finite ActorType] [Finite GroupType] [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (primes : Set ℕ) (subgroup hall : Subgroup GroupType)
    (supported : primeSupported primes (Nat.card subgroup))
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup)
    (fixed_normalizes : FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (subgroup : Set GroupType))
    (hall_property : IsHallSubgroup primes hall)
    (hall_invariant : ∀ actorElement : ActorType, ∀ element ∈ hall,
      actorElement • element ∈ hall) : subgroup ≤ hall := by
  obtain ⟨other, contains, other_hall, other_invariant⟩ := invariant_hall_subgroup_containing
    prime prime_prime ActorType actor_pgroup GroupType coprime primes subgroup supported invariant
  obtain ⟨element, conjugates, fixed⟩ := invariant_hall_subgroups_conjugate_by_fixed_element prime
    prime_prime ActorType actor_pgroup GroupType coprime primes other hall other_hall hall_property
    other_invariant hall_invariant
  have subgroup_preserved : conjugateSubgroup element subgroup = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (fixed_normalizes fixed)
  have mapped_contains := Subgroup.map_mono (f := (MulAut.conj element).toMonoidHom) contains
  change conjugateSubgroup element subgroup ≤ conjugateSubgroup element other at mapped_contains
  rwa [subgroup_preserved, conjugates] at mapped_contains

theorem fixed_normalized_prime_hull_properties
    [Finite ActorType] [Finite GroupType] [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) (primes : Set ℕ) :
    primeSupported primes (Nat.card (fixedNormalizedPrimeHull (ActorType := ActorType)
      (GroupType := GroupType) primes)) ∧
    (∀ actorElement : ActorType,
      ∀ element ∈ fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := GroupType) primes,
        actorElement • element ∈ fixedNormalizedPrimeHull (ActorType := ActorType)
          (GroupType := GroupType) primes) ∧
    FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer
      (fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := GroupType) primes :
        Set GroupType) := by
  classical
  let hull := fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := GroupType) primes
  have bottom_supported : primeSupported primes (Nat.card (⊥ : Subgroup GroupType)) := by
    rw [(Subgroup.eq_bot_iff_card _).mp rfl]
    exact prime_supported_one primes
  have bottom_invariant : ∀ actorElement : ActorType, ∀ element ∈ (⊥ : Subgroup GroupType),
      actorElement • element ∈ (⊥ : Subgroup GroupType) := by
    intro actorElement element member
    rw [Subgroup.mem_bot.mp member, smul_one]
    exact Subgroup.one_mem _
  obtain ⟨hall, _, hall_property, hall_invariant⟩ := invariant_hall_subgroup_containing prime
    prime_prime ActorType actor_pgroup GroupType coprime primes ⊥ bottom_supported bottom_invariant
  have hull_le : hull ≤ hall := by
    apply iSup_le
    intro subgroup
    apply iSup_le
    intro property
    exact fixed_normalized_prime_subgroup_le_invariant_hall prime prime_prime actor_pgroup
      coprime primes subgroup hall property.1 property.2.1 property.2.2 hall_property hall_invariant
  refine ⟨prime_supported_of_dvd primes hall_property.1 (Subgroup.card_dvd_of_le hull_le), ?_, ?_⟩
  · intro actorElement element member
    have mapped_le : hull.map (MulDistribMulAction.toMonoidHom GroupType actorElement) ≤ hull := by
      change (fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := GroupType) primes).map
        (MulDistribMulAction.toMonoidHom GroupType actorElement) ≤ hull
      rw [fixedNormalizedPrimeHull, Subgroup.map_iSup]
      apply iSup_le
      intro subgroup
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro property
      apply le_trans _ (le_iSup_of_le subgroup (le_iSup_of_le property le_rfl))
      rintro value ⟨representative, representative_member, rfl⟩
      exact property.2.1 actorElement representative representative_member
    exact mapped_le (Subgroup.mem_map_of_mem _ member)
  · apply normalizer_iSup_of_le
    intro subgroup
    apply normalizer_iSup_of_le
    intro property
    exact property.2.2

theorem fixed_normalized_prime_hull_contains (primes : Set ℕ) (subgroup : Subgroup GroupType)
    (supported : primeSupported primes (Nat.card subgroup))
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup)
    (fixed_normalizes : FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (subgroup : Set GroupType)) :
    subgroup ≤ fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := GroupType) primes :=
  le_iSup_of_le subgroup (le_iSup_of_le ⟨supported, invariant, fixed_normalizes⟩ le_rfl)

end CFSG.SignalizerFunctor.Helpers
