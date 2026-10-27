module

public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalIncompleteSolvable

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem solvable_signalizer_completion_congr (prime rank : ℕ) (actor : Subgroup GroupType)
    (first second : Subgroup GroupType → Subgroup GroupType)
    (equal : ∀ selected ∈ signalizerFunctorEk prime rank actor, first selected = second selected) :
    solvableSignalizerCompatible prime rank actor first
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, first selected) ↔
    solvableSignalizerCompatible prime rank actor second
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, second selected) := by
  have completion_equal := signalizer_completion_congr_values prime rank actor first second equal
  unfold solvableSignalizerCompatible
  rw [← completion_equal]
  exact and_congr (signalizer_compatible_congr_values prime rank actor first second equal _) Iff.rfl

omit [Finite GroupType] in
theorem solvable_signalizer_restriction_complete_of_compatible (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (normalized : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values selected : Set GroupType))
    (complete : solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected)) :
    solvableSignalizerCompatible prime rank actor (signalizerRestriction values ambient)
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, signalizerRestriction values ambient selected) := by
  let := complete.2
  have contained : (⨆ selected ∈ signalizerFunctorEk prime rank actor,
      signalizerRestriction values ambient selected) ≤
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) := by
    apply iSup_le
    intro selected
    apply iSup_le
    intro member
    exact inf_le_left.trans (signalizer_value_le_completion prime rank actor values member)
  exact ⟨signalizer_restriction_complete_of_compatible prime rank actor ambient values ambient_normalized
    normalized complete.1,
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective contained)⟩

theorem solvable_signalizer_normalized_restriction_locally_complete
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor ambient : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤
      Subgroup.normalizer (ambient : Set GroupType)) :
    solvableSignalizerLocallyComplete prime rank actor (signalizerRestriction values ambient) := by
  let restrictedValues := signalizerRestriction values ambient
  have spectrum_subset := signalizer_spectrum_of_le prime rank actor values restrictedValues
    (fun _ _ => inf_le_left)
  refine ⟨?_, ?_⟩
  · intro target nontrivial compatible
    have original_compatible := (signalizer_restriction_compatible_iff prime rank prime_prime actor
      ambient target elementary large values conditions.coprime).mp compatible.1
    let normalizer := Subgroup.normalizer (target : Set GroupType)
    let normalizerValues := signalizerRestriction values normalizer
    have original_complete := locally_complete.1 target nontrivial ⟨original_compatible.1, compatible.2⟩
    have normalizer_complete : solvableSignalizerCompatible prime rank actor normalizerValues
        (⨆ selected ∈ signalizerFunctorEk prime rank actor, normalizerValues selected) :=
      ⟨(signalizer_restriction_compatible_of_le prime rank actor normalizer _ values
        (iSup_le fun _ => iSup_le fun _ => inf_le_right)).mpr original_complete.1, original_complete.2⟩
    have normalizer_normalized := normalizer_normalized actor target original_compatible.1.1
    have doubly_complete := solvable_signalizer_restriction_complete_of_compatible prime rank actor
      ambient normalizerValues ambient_normalized
      (fun selected member => normalizer_inf_of_le actor _ _ (conditions.normalized selected member)
        normalizer_normalized) normalizer_complete
    have value_equal : ∀ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerRestriction normalizerValues ambient selected =
          signalizerRestriction restrictedValues normalizer selected := by
      intro selected _
      exact inf_right_comm (values selected) normalizer ambient
    have rewritten := (solvable_signalizer_completion_congr prime rank actor _ _ value_equal).mp
      doubly_complete
    exact ⟨(signalizer_restriction_compatible_of_le prime rank actor normalizer _ restrictedValues
      (iSup_le fun _ => iSup_le fun _ => inf_le_right)).mp rewritten.1, rewritten.2⟩
  · intro groupPrime prime_member
    let originalPrimes := signalizerSpectrum prime rank actor values \ {groupPrime}
    let restrictedPrimes := signalizerSpectrum prime rank actor restrictedValues \ {groupPrime}
    let originalPrimeValues := signalizerPrimeValue prime rank actor values originalPrimes
    let restrictedPrimeValues := signalizerPrimeValue prime rank actor restrictedValues restrictedPrimes
    have original_complete := locally_complete.2 groupPrime (spectrum_subset prime_member)
    have original_prime_conditions := solvable_signalizer_prime_subfunctor_conditions prime rank
      prime_prime actor elementary values conditions originalPrimes
    have restricted_complete := solvable_signalizer_restriction_complete_of_compatible prime rank actor
      ambient originalPrimeValues ambient_normalized original_prime_conditions.normalized original_complete
    have value_equal : ∀ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerRestriction originalPrimeValues ambient selected = restrictedPrimeValues selected := by
      intro selected member
      rw [show signalizerRestriction originalPrimeValues ambient selected =
        originalPrimeValues selected ⊓ ambient from rfl,
        ← signalizer_prime_subfunctor_restriction prime rank prime_prime actor ambient elementary values
          conditions ambient_normalized common_normalized originalPrimes selected member]
      apply signalizer_prime_value_eq_of_prime_support_agrees
      intro candidate contained
      constructor
      · intro supported groupDivisor divisor_prime divides
        have original_member := supported groupDivisor divisor_prime divides
        exact ⟨⟨divisor_prime, selected, member,
          divides.trans (Subgroup.card_dvd_of_le contained)⟩, original_member.2⟩
      · intro supported groupDivisor divisor_prime divides
        have restricted_member := supported groupDivisor divisor_prime divides
        exact ⟨spectrum_subset restricted_member.1, restricted_member.2⟩
    exact (solvable_signalizer_completion_congr prime rank actor _ _ value_equal).mp restricted_complete

end CFSG.SignalizerFunctor.Helpers
