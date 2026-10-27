module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerSpectrum
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSubfunctorRestriction

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

@[expose] def signalizerLocallyComplete (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) : Prop :=
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
          (signalizerSpectrum prime rank actor values \ {groupPrime}) selected))

omit [Finite GroupType] in
theorem signalizer_compatible_congr_values (prime rank : ℕ) (actor : Subgroup GroupType)
    (first second : Subgroup GroupType → Subgroup GroupType)
    (equal : ∀ selected ∈ signalizerFunctorEk prime rank actor, first selected = second selected)
    (target : Subgroup GroupType) :
    signalizerCompatible prime rank actor first target ↔
      signalizerCompatible prime rank actor second target := by
  constructor
  · intro compatible
    refine ⟨compatible.1, ?_⟩
    intro selected member
    rw [← equal selected member]
    exact compatible.2 selected member
  · intro compatible
    refine ⟨compatible.1, ?_⟩
    intro selected member
    rw [equal selected member]
    exact compatible.2 selected member

omit [Finite GroupType] in
theorem signalizer_completion_congr_values (prime rank : ℕ) (actor : Subgroup GroupType)
    (first second : Subgroup GroupType → Subgroup GroupType)
    (equal : ∀ selected ∈ signalizerFunctorEk prime rank actor, first selected = second selected) :
    (⨆ selected ∈ signalizerFunctorEk prime rank actor, first selected) =
      ⨆ selected ∈ signalizerFunctorEk prime rank actor, second selected := by
  congr 1
  funext selected
  congr 1
  funext member
  exact equal selected member

omit [Finite GroupType] in
theorem signalizer_restriction_complete_of_compatible (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (normalized : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values selected : Set GroupType))
    (complete : signalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected)) :
    signalizerCompatible prime rank actor (signalizerRestriction values ambient)
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, signalizerRestriction values ambient selected) := by
  have completion_le : (⨆ selected ∈ signalizerFunctorEk prime rank actor,
      signalizerRestriction values ambient selected) ≤
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ⊓ ambient := by
    apply iSup_le
    intro selected
    apply iSup_le
    intro member
    exact le_inf (inf_le_left.trans (signalizer_value_le_completion prime rank actor values member))
      inf_le_right
  refine ⟨signalizer_completion_normalized prime rank actor (signalizerRestriction values ambient)
    (fun selected member => normalizer_inf_of_le actor _ _ (normalized selected member)
      ambient_normalized), ?_⟩
  intro selected member
  exact le_inf ((inf_le_inf_right _ (completion_le.trans inf_le_left)).trans
    (complete.2 selected member)) (inf_le_left.trans (completion_le.trans inf_le_right))

omit [Finite GroupType] in
theorem signalizer_prime_value_eq_of_prime_support_agrees (prime rank : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (first second : Set ℕ) (selected : Subgroup GroupType)
    (agrees : ∀ candidate ≤ values selected,
      primeSupported first (Nat.card candidate) ↔ primeSupported second (Nat.card candidate)) :
    signalizerPrimeValue prime rank actor values first selected =
      signalizerPrimeValue prime rank actor values second selected := by
  apply le_antisymm
  · apply iSup_le
    intro candidate
    apply iSup_le
    intro property
    exact signalizer_prime_value_contains prime rank actor values second selected candidate property.1
      ((agrees candidate property.1).mp property.2.1) property.2.2.1 property.2.2.2
  · apply iSup_le
    intro candidate
    apply iSup_le
    intro property
    exact signalizer_prime_value_contains prime rank actor values first selected candidate property.1
      ((agrees candidate property.1).mpr property.2.1) property.2.2.1 property.2.2.2

theorem signalizer_normalized_restriction_locally_complete
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor ambient : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : signalizerLocallyComplete prime rank actor values)
    (ambient_normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤
      Subgroup.normalizer (ambient : Set GroupType)) :
    signalizerLocallyComplete prime rank actor (signalizerRestriction values ambient) := by
  let restrictedValues := signalizerRestriction values ambient
  have restricted_properties := signalizer_restriction_properties prime rank actor ambient values
    ambient_normalized conditions.central conditions.coprime conditions.normalized conditions.balanced
  have spectrum_subset := signalizer_spectrum_of_le prime rank actor values restrictedValues
    (fun _ _ => inf_le_left)
  refine ⟨?_, ?_⟩
  · intro target nontrivial compatible
    have original_compatible := (signalizer_restriction_compatible_iff prime rank prime_prime actor
      ambient target elementary large values conditions.coprime).mp compatible
    let normalizer := Subgroup.normalizer (target : Set GroupType)
    let normalizerValues := signalizerRestriction values normalizer
    have original_complete := locally_complete.1 target nontrivial original_compatible.1
    have normalizer_complete : signalizerCompatible prime rank actor normalizerValues
        (⨆ selected ∈ signalizerFunctorEk prime rank actor, normalizerValues selected) :=
      (signalizer_restriction_compatible_of_le prime rank actor normalizer _ values
        (iSup_le fun _ => iSup_le fun _ => inf_le_right)).mpr original_complete
    have normalizer_normalized := normalizer_normalized actor target original_compatible.1.1
    have doubly_complete := signalizer_restriction_complete_of_compatible prime rank actor ambient
      normalizerValues ambient_normalized
      (fun selected member => normalizer_inf_of_le actor _ _ (conditions.normalized selected member)
        normalizer_normalized) normalizer_complete
    have value_equal : ∀ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerRestriction normalizerValues ambient selected =
          signalizerRestriction restrictedValues normalizer selected := by
      intro selected _
      change (values selected ⊓ normalizer) ⊓ ambient = (values selected ⊓ ambient) ⊓ normalizer
      exact inf_right_comm (values selected) normalizer ambient
    rw [signalizer_completion_congr_values prime rank actor _ _ value_equal] at doubly_complete
    have rewritten := (signalizer_compatible_congr_values prime rank actor _ _ value_equal _).mp
      doubly_complete
    exact (signalizer_restriction_compatible_of_le prime rank actor normalizer _ restrictedValues
      (iSup_le fun _ => iSup_le fun _ => inf_le_right)).mp rewritten
  · intro groupPrime prime_member
    let originalPrimes := signalizerSpectrum prime rank actor values \ {groupPrime}
    let restrictedPrimes := signalizerSpectrum prime rank actor restrictedValues \ {groupPrime}
    let originalPrimeValues := signalizerPrimeValue prime rank actor values originalPrimes
    let restrictedPrimeValues := signalizerPrimeValue prime rank actor restrictedValues restrictedPrimes
    have original_complete := locally_complete.2 groupPrime (spectrum_subset prime_member)
    have original_prime_conditions := solvable_signalizer_prime_subfunctor_conditions prime rank
      prime_prime actor elementary values conditions originalPrimes
    have restricted_complete := signalizer_restriction_complete_of_compatible prime rank actor ambient
      originalPrimeValues ambient_normalized original_prime_conditions.normalized original_complete
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
    rw [signalizer_completion_congr_values prime rank actor _ _ value_equal] at restricted_complete
    exact (signalizer_compatible_congr_values prime rank actor _ _ value_equal _).mp restricted_complete

end CFSG.SignalizerFunctor.Helpers
