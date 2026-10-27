module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerConditions
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientPrimeHullRestriction

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem signalizer_prime_subfunctor_restriction
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor ambient : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤
      Subgroup.normalizer (ambient : Set GroupType)) (primes : Set ℕ)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    signalizerPrimeValue prime rank actor (signalizerRestriction values ambient) primes selected =
      signalizerPrimeValue prime rank actor values primes selected ⊓ ambient := by
  let restrictedValues := signalizerRestriction values ambient
  have restricted_properties := signalizer_restriction_properties prime rank actor ambient values
    ambient_normalized conditions.central conditions.coprime conditions.normalized conditions.balanced
  have restricted_solvable := signalizer_restriction_solvable prime rank actor ambient values
    conditions.solvable
  let target := values selected
  let restrictedTarget := target ⊓ ambient
  have target_normalized := conditions.normalized selected member
  have restricted_normalized := (restricted_properties.1 selected member).2.2
  let _targetAction := conjugationAction actor target target_normalized
  let _restrictedAction := conjugationAction actor restrictedTarget restricted_normalized
  have restricted_fixed_normalized : target ⊓ Subgroup.centralizer (actor : Set GroupType) ≤
      Subgroup.normalizer (restrictedTarget : Set GroupType) := by
    rw [signalizer_value_common_fixed prime rank actor values conditions.balanced member]
    exact normalizer_inf_of_le _ target ambient
      ((le_of_eq (signalizer_value_common_fixed prime rank actor values conditions.balanced member).symm)
        |>.trans inf_le_left |>.trans Subgroup.le_normalizer) common_normalized
  have hull_restriction := ambient_fixed_normalized_prime_hull_restriction prime prime_prime actor
    target restrictedTarget (elementary_abelian_isPGroup prime actor elementary) inf_le_left
    target_normalized restricted_normalized (conditions.coprime selected member)
    (conditions.solvable selected member) restricted_fixed_normalized primes
  have original_hull := signalizer_prime_value_eq_fixed_hull prime rank prime_prime actor elementary
    values primes conditions.balanced selected member (conditions.coprime selected member)
    target_normalized (conditions.solvable selected member)
  have restricted_hull := signalizer_prime_value_eq_fixed_hull prime rank prime_prime actor elementary
    restrictedValues primes restricted_properties.2 selected member
    (restricted_properties.1 selected member).2.1 restricted_normalized
    (restricted_solvable selected member)
  change signalizerPrimeValue prime rank actor restrictedValues primes selected = _
  calc
    signalizerPrimeValue prime rank actor restrictedValues primes selected =
        (fixedNormalizedPrimeHull (ActorType := actor) (GroupType := restrictedTarget) primes).map
          restrictedTarget.subtype := restricted_hull
    _ = (fixedNormalizedPrimeHull (ActorType := actor) (GroupType := target) primes).map
          target.subtype ⊓ restrictedTarget := hull_restriction
    _ = signalizerPrimeValue prime rank actor values primes selected ⊓ ambient := by
      rw [← original_hull]
      change signalizerPrimeValue prime rank actor values primes selected ⊓ (target ⊓ ambient) = _
      rw [← inf_assoc, inf_eq_left.mpr (signalizer_prime_value_le prime rank actor values primes selected)]

end CFSG.SignalizerFunctor.Helpers
