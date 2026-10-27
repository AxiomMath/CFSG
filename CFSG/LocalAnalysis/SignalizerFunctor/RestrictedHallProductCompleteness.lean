module

public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableLocalRestriction
public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianHallProductCompleteness

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem solvable_signalizer_restriction_conditions
    (prime rank : ℕ) (actor parent : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType)) :
    SolvableSignalizerConditions prime rank actor (signalizerRestriction values parent) := by
  have properties := signalizer_restriction_properties prime rank actor parent values normalized
    conditions.central conditions.coprime conditions.normalized conditions.balanced
  exact ⟨fun selected member => (properties.1 selected member).1,
    fun selected member => (properties.1 selected member).2.1,
    fun selected member => (properties.1 selected member).2.2, properties.2,
    signalizer_restriction_solvable prime rank actor parent values conditions.solvable⟩

theorem restricted_prime_deleted_value_spectrum
    (prime rank groupPrime : ℕ) (actor parent : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    signalizerPrimeValue prime rank actor (signalizerRestriction values parent)
      (signalizerSpectrum prime rank actor (signalizerRestriction values parent) \ {groupPrime}) selected =
    signalizerPrimeValue prime rank actor (signalizerRestriction values parent)
      (signalizerSpectrum prime rank actor values \ {groupPrime}) selected := by
  have spectrum_subset := signalizer_spectrum_of_le prime rank actor values
    (signalizerRestriction values parent) (fun _ _ => inf_le_left)
  apply signalizer_prime_value_eq_of_prime_support_agrees
  intro candidate candidate_le
  constructor
  · intro supported divisor divisor_prime divides
    have prime_member := supported divisor divisor_prime divides
    exact ⟨spectrum_subset prime_member.1, prime_member.2⟩
  · intro supported divisor divisor_prime divides
    exact ⟨⟨divisor_prime, selected, member,
      divides.trans (Subgroup.card_dvd_of_le candidate_le)⟩,
      (supported divisor divisor_prime divides).2⟩

theorem restricted_prime_deleted_completion
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (actor parent : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤
      Subgroup.normalizer (parent : Set GroupType))
    (completion_le : signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime}) ≤ parent) :
    signalizerPrimeCompletion prime rank actor (signalizerRestriction values parent)
      (signalizerSpectrum prime rank actor (signalizerRestriction values parent) \ {groupPrime}) =
    signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime}) := by
  apply signalizer_completion_congr_values
  intro selected member
  rw [restricted_prime_deleted_value_spectrum prime rank groupPrime actor parent values selected member,
    signalizer_prime_subfunctor_restriction prime rank prime_prime actor parent elementary values
      conditions normalized common_normalized _ selected member]
  exact inf_eq_left.mpr ((signalizer_value_le_completion prime rank actor
    (signalizerPrimeValue prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime})) member).trans completion_le)

theorem restricted_abelian_hall_product_solvable_compatible
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor parent factor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (factor_compatible : signalizerCompatible prime rank actor values factor)
    (factor_pgroup : IsPGroup groupPrime factor) (abelian : IsMulCommutative factor)
    (factor_nontrivial : factor ≠ ⊥)
    (common_normalized : signalizerCommonFixed prime rank actor values ≤
      Subgroup.normalizer (parent : Set GroupType))
    (whole : subgroupProduct
      (signalizerPrimeCompletion prime rank actor values
        (signalizerSpectrum prime rank actor values \ {groupPrime})) factor = (parent : Set GroupType)) :
    solvableSignalizerCompatible prime rank actor values parent := by
  have generation_large : prime ^ (rank + 1) ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (by omega : rank + 1 ≤ rank + 2)).trans large
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  have factor_divides : groupPrime ∣ Nat.card factor := by
    rcases factor_pgroup.card_eq_or_dvd with cardinality | divides
    · exact (factor_nontrivial ((Subgroup.eq_bot_iff_card factor).mpr cardinality)).elim
    · exact divides
  obtain ⟨selected, member, value_divides⟩ := signalizer_compatible_prime_support prime rank groupPrime
    prime_prime groupPrime_prime actor elementary generation_large values conditions.coprime factor
    factor_compatible factor_divides
  have prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values :=
    ⟨groupPrime_prime, selected, member, value_divides⟩
  have control := locally_complete_prime_deleted_control prime rank prime_prime actor elementary
    generation_large values conditions locally_complete groupPrime prime_member
  have properties := normalized_product_parent_properties actor parent _ factor control.1.1.1
    factor_compatible.1 whole
  let restrictedValues := signalizerRestriction values parent
  have restricted_conditions := solvable_signalizer_restriction_conditions prime rank actor parent
    values conditions properties.2.2
  have restricted_local := solvable_signalizer_normalized_restriction_locally_complete prime rank
    prime_prime actor parent elementary generation_large values conditions locally_complete properties.2.2
    common_normalized
  have restricted_factor := (signalizer_restriction_compatible_of_le prime rank actor parent factor
    values properties.2.1).mpr factor_compatible
  obtain ⟨restrictedSelected, restricted_member, restricted_divides⟩ := signalizer_compatible_prime_support
    prime rank groupPrime prime_prime groupPrime_prime actor elementary generation_large restrictedValues
    restricted_conditions.coprime factor restricted_factor factor_divides
  have restricted_prime_member : groupPrime ∈ signalizerSpectrum prime rank actor restrictedValues :=
    ⟨groupPrime_prime, restrictedSelected, restricted_member, restricted_divides⟩
  have completion_equal := restricted_prime_deleted_completion prime rank groupPrime prime_prime actor
    parent elementary values conditions properties.2.2 common_normalized properties.1
  have restricted_whole : subgroupProduct
      (signalizerPrimeCompletion prime rank actor restrictedValues
        (signalizerSpectrum prime rank actor restrictedValues \ {groupPrime})) factor =
      (parent : Set GroupType) := by
    rw [completion_equal]
    exact whole
  have complete := abelian_hall_product_complete prime rank groupPrime prime_prime groupPrime_prime
    actor parent factor elementary large restrictedValues restricted_conditions restricted_local
    restricted_prime_member restricted_factor factor_pgroup abelian (fun _ _ => inf_le_right) restricted_whole
  exact ⟨(signalizer_restriction_compatible_of_le prime rank actor parent parent values le_rfl).mp
    complete.2.1, complete.2.2⟩

end CFSG.SignalizerFunctor.Helpers
