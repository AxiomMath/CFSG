module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeTransitivity
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageCompleteness
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerSpectrum
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerConditions

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem minimal_incomplete_solvable_signalizer_local
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (incomplete : ¬ signalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected))
    (smaller_complete : ∀ (SmallerType : Type groupUniverse) [Group SmallerType] [Finite SmallerType]
      (smallerActor : Subgroup SmallerType), IsElemAbelian prime smallerActor →
      prime ^ (rank + 2) ≤ Nat.card smallerActor →
      ∀ smallerValues : Subgroup SmallerType → Subgroup SmallerType,
        SolvableSignalizerConditions prime rank smallerActor smallerValues →
        Nat.card SmallerType + (signalizerSpectrum prime rank smallerActor smallerValues).ncard <
          Nat.card GroupType + (signalizerSpectrum prime rank actor values).ncard →
        signalizerCompatible prime rank smallerActor smallerValues
          (⨆ selected ∈ signalizerFunctorEk prime rank smallerActor, smallerValues selected)) :
    (∀ normal : Subgroup GroupType, normal.Normal →
      signalizerCompatible prime rank actor values normal → normal = ⊥) ∧
    (∀ target : Subgroup GroupType, target ≠ ⊥ →
      signalizerCompatible prime rank actor values target →
      signalizerCompatible prime rank actor values
        (⨆ selected ∈ signalizerFunctorEk prime rank actor,
          signalizerRestriction values (Subgroup.normalizer (target : Set GroupType)) selected)) ∧
    (∀ groupPrime ∈ signalizerSpectrum prime rank actor values,
      signalizerCompatible prime rank actor
        (signalizerPrimeValue prime rank actor values
          (signalizerSpectrum prime rank actor values \ {groupPrime}))
        (⨆ selected ∈ signalizerFunctorEk prime rank actor,
          signalizerPrimeValue prime rank actor values
            (signalizerSpectrum prime rank actor values \ {groupPrime}) selected)) := by
  have generation_large : prime ^ (rank + 1) ≤ Nat.card actor := by
    apply le_trans _ large
    rw [show rank + 2 = (rank + 1) + 1 by omega, pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ generation_large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have spectrum_finite := signalizer_spectrum_finite prime rank actor values
  have no_normal : ∀ normal : Subgroup GroupType, normal.Normal →
      signalizerCompatible prime rank actor values normal → normal = ⊥ := by
    intro normal normal_normal compatible
    by_contra nontrivial
    let := normal_normal
    let projection := QuotientGroup.mk' normal
    have kernel_compatible : signalizerCompatible prime rank actor values projection.ker := by
      change signalizerCompatible prime rank actor values (QuotientGroup.mk' normal).ker
      rwa [QuotientGroup.ker_mk']
    have kernel_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
      rank_large values conditions.coprime projection.ker kernel_compatible.1 kernel_compatible.2
    have actor_injective := actor_image_injective_of_coprime_kernel prime prime_prime projection
      actor (elementary_abelian_isPGroup prime actor elementary) kernel_coprime
    have actor_card := subgroup_image_card_of_injective projection actor actor_injective
    have quotient_conditions := solvable_signalizer_image_conditions prime rank prime_prime
      projection actor elementary actor_injective values conditions
    have quotient_spectrum_subset := signalizer_image_spectrum prime rank projection actor
      actor_injective values
    have spectrum_card_le := Set.ncard_le_ncard quotient_spectrum_subset spectrum_finite
    have quotient_card_lt := normal_quotient_card_strict normal nontrivial
    have quotient_complete := smaller_complete (GroupType ⧸ normal) (actor.map projection)
      (elementary_abelian_image prime projection actor elementary) (by rwa [actor_card])
      (signalizerImageValues projection actor values) quotient_conditions (by omega)
    exact incomplete ((signalizer_image_completion_compatible_iff prime rank prime_prime projection
      actor elementary generation_large values conditions.coprime conditions.normalized
      kernel_compatible).mpr quotient_complete)
  refine ⟨no_normal, ?_, ?_⟩
  · intro target nontrivial compatible
    let ambient := Subgroup.normalizer (target : Set GroupType)
    have ambient_ne_top : ambient ≠ ⊤ := by
      intro equal
      exact nontrivial (no_normal target (Subgroup.normalizer_eq_top_iff.mp equal) compatible)
    have ambient_card_lt : Nat.card ambient < Nat.card GroupType := by
      have proper : ambient < ⊤ := lt_top_iff_ne_top.mpr ambient_ne_top
      simpa only [Subgroup.card_top] using subgroup_card_strict_mono proper
    have actor_contained : actor ≤ ambient := compatible.1
    have actor_card := Nat.card_congr (Subgroup.subgroupOfEquivOfLe actor_contained).toEquiv
    have ambient_conditions := solvable_signalizer_subgroup_conditions prime rank actor ambient
      actor_contained values conditions
    have ambient_spectrum_subset := signalizer_subgroup_spectrum prime rank actor ambient
      actor_contained values
    have spectrum_card_le := Set.ncard_le_ncard ambient_spectrum_subset spectrum_finite
    have ambient_complete := smaller_complete ambient (actor.subgroupOf ambient)
      (elementary_abelian_subgroupOf prime actor ambient elementary) (by rwa [actor_card])
      (signalizerSubgroupValues ambient values) ambient_conditions (by omega)
    exact (signalizer_subgroup_completion_compatible_iff prime rank actor ambient actor_contained
      values).mp ambient_complete
  · intro groupPrime prime_member
    let primes := signalizerSpectrum prime rank actor values \ {groupPrime}
    let primeValues := signalizerPrimeValue prime rank actor values primes
    have prime_conditions := solvable_signalizer_prime_subfunctor_conditions prime rank prime_prime
      actor elementary values conditions primes
    have prime_spectrum_subset := signalizer_prime_subfunctor_spectrum prime rank prime_prime actor
      elementary values primes conditions.coprime conditions.normalized conditions.balanced
      conditions.solvable
    have spectrum_subset : signalizerSpectrum prime rank actor primeValues ⊆
        signalizerSpectrum prime rank actor values := fun _ member => (prime_spectrum_subset member).1
    have prime_not_member : groupPrime ∉ signalizerSpectrum prime rank actor primeValues := by
      intro member
      exact (prime_spectrum_subset member).2.2 (Set.mem_singleton groupPrime)
    have spectrum_strict : signalizerSpectrum prime rank actor primeValues ⊂
        signalizerSpectrum prime rank actor values :=
      (Set.ssubset_iff_of_subset spectrum_subset).mpr ⟨groupPrime, prime_member, prime_not_member⟩
    have spectrum_card_lt := Set.ncard_lt_ncard spectrum_strict spectrum_finite
    exact smaller_complete GroupType actor elementary large primeValues prime_conditions (by omega)

end CFSG.SignalizerFunctor.Helpers
