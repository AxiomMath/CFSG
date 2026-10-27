module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableActorSylow

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem normalized_solvable_actor_sylow_containing
    (prime : ℕ) (prime_prime : prime.Prime) (actor parent target : Subgroup GroupType)
    (actor_solvable : Group.IsSolvable actor) (parent_solvable : Group.IsSolvable parent)
    (coprime : Nat.Coprime (Nat.card actor) (Nat.card parent))
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (target_le : target ≤ parent) (target_pgroup : IsPGroup prime target)
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    ∃ sylow : Sylow prime parent, target ≤ (sylow : Subgroup parent).map parent.subtype ∧
      actor ≤ Subgroup.normalizer
        (((sylow : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType) := by
  let := actor_solvable
  let := parent_solvable
  let _action := conjugationAction actor parent parent_normalized
  have internal_pgroup : IsPGroup prime (target.subgroupOf parent) :=
    target_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe target_le).symm
  have internal_invariant := normalized_subgroupOf_invariant actor parent target parent_normalized target_normalized
  obtain ⟨sylow, contains, invariant⟩ := solvable_actor_invariant_sylow_containing actor parent prime prime_prime
    coprime (target.subgroupOf parent) internal_pgroup internal_invariant
  refine ⟨sylow, ?_, invariant_subgroup_map_normalized actor parent parent_normalized _ invariant⟩
  have mapped := Subgroup.map_mono (f := parent.subtype) contains
  rwa [Subgroup.map_subgroupOf_eq_of_le target_le] at mapped

theorem solvable_two_prime_actor (prime groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (actor secondActor : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor) (second_pgroup : IsPGroup groupPrime secondActor)
    (normalized : actor ≤ Subgroup.normalizer (secondActor : Set GroupType)) :
    Group.IsSolvable (actor ⊔ secondActor : Subgroup GroupType) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let _actorNilpotent := actor_pgroup.isNilpotent
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  let _secondNilpotent := second_pgroup.isNilpotent
  rw [sup_comm]
  exact solvable_sup_of_normalizing secondActor actor normalized inferInstance inferInstance

theorem two_prime_actor_card_coprime (prime groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (actor secondActor parent : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor) (second_pgroup : IsPGroup groupPrime secondActor)
    (normalized : actor ≤ Subgroup.normalizer (secondActor : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card parent))
    (second_coprime : Nat.Coprime groupPrime (Nat.card parent)) :
    Nat.Coprime (Nat.card (actor ⊔ secondActor : Subgroup GroupType)) (Nat.card parent) := by
  have actor_supported : primeSupported {prime, groupPrime} (Nat.card actor) := by
    intro divisor divisor_prime divides
    have equal := (prime_supported_singleton_iff_pgroup prime prime_prime actor).mpr actor_pgroup
      divisor divisor_prime divides
    exact Or.inl equal
  have second_supported : primeSupported {prime, groupPrime} (Nat.card secondActor) := by
    intro divisor divisor_prime divides
    have equal := (prime_supported_singleton_iff_pgroup groupPrime groupPrime_prime secondActor).mpr second_pgroup
      divisor divisor_prime divides
    exact Or.inr equal
  have combined_supported : primeSupported {prime, groupPrime} (Nat.card (actor ⊔ secondActor : Subgroup GroupType)) := by
    rw [sup_comm]
    exact prime_supported_sup_of_normalizing {prime, groupPrime} secondActor actor normalized second_supported actor_supported
  apply prime_supported_coprime {prime, groupPrime} combined_supported
  intro divisor divisor_prime divides member
  rcases member with same | same
  · exact prime_prime.coprime_iff_not_dvd.mp coprime (same ▸ divides)
  · have equality : divisor = groupPrime := same
    exact groupPrime_prime.coprime_iff_not_dvd.mp second_coprime (equality ▸ divides)

theorem jointly_normalized_sylow_containing
    (prime groupPrime sylowPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (sylowPrime_prime : sylowPrime.Prime) (actor secondActor parent target : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor) (second_pgroup : IsPGroup groupPrime secondActor)
    (second_normalized : actor ≤ Subgroup.normalizer (secondActor : Set GroupType))
    (parent_solvable : Group.IsSolvable parent)
    (coprime : Nat.Coprime prime (Nat.card parent))
    (second_coprime : Nat.Coprime groupPrime (Nat.card parent))
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (parent_second_normalized : secondActor ≤ Subgroup.normalizer (parent : Set GroupType))
    (target_le : target ≤ parent) (target_pgroup : IsPGroup sylowPrime target)
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (target_second_normalized : secondActor ≤ Subgroup.normalizer (target : Set GroupType)) :
    ∃ sylow : Sylow sylowPrime parent, target ≤ (sylow : Subgroup parent).map parent.subtype ∧
      actor ≤ Subgroup.normalizer
        (((sylow : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType) ∧
      secondActor ≤ Subgroup.normalizer
        (((sylow : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType) := by
  obtain ⟨sylow, contains, normalized⟩ := normalized_solvable_actor_sylow_containing sylowPrime sylowPrime_prime
    (actor ⊔ secondActor) parent target
    (solvable_two_prime_actor prime groupPrime prime_prime groupPrime_prime actor secondActor actor_pgroup second_pgroup
      second_normalized) parent_solvable
    (two_prime_actor_card_coprime prime groupPrime prime_prime groupPrime_prime actor secondActor parent actor_pgroup
      second_pgroup second_normalized coprime second_coprime)
    (sup_le parent_normalized parent_second_normalized) target_le target_pgroup
    (sup_le target_normalized target_second_normalized)
  exact ⟨sylow, contains, le_sup_left.trans normalized, le_sup_right.trans normalized⟩

end CFSG.SignalizerFunctor.Helpers
