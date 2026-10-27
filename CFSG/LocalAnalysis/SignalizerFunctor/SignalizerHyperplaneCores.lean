module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorization

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

@[expose] def signalizerHyperplaneCore (prime rank groupPrime : ℕ) (actor hyperplane : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) : Subgroup GroupType :=
  ⨆ selected ∈ signalizerFunctorEk prime rank actor, ⨆ (_ : selected ≤ hyperplane),
    (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype

def signalizerHyperplaneCommonFixed (prime rank : ℕ) (actor hyperplane : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) : Subgroup GroupType :=
  Subgroup.centralizer (hyperplane : Set GroupType) ⊓
    ⨅ selected ∈ signalizerFunctorEk prime rank actor, ⨅ (_ : selected ≤ hyperplane), values selected

omit [Finite GroupType] in
theorem signalizer_hyperplane_core_contains (prime rank groupPrime : ℕ)
    (actor hyperplane : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor)
    (contained : selected ≤ hyperplane) :
    (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ≤
      signalizerHyperplaneCore prime rank groupPrime actor hyperplane values :=
  le_iSup_of_le selected (le_iSup_of_le member (le_iSup_of_le contained le_rfl))

theorem signalizer_hyperplane_core_properties
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor hyperplane : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values) :
    let core := signalizerHyperplaneCore prime rank groupPrime actor hyperplane values
    core ≤ signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime}) ∧
    actor ≤ Subgroup.normalizer (core : Set GroupType) ∧
    signalizerHyperplaneCommonFixed prime rank actor hyperplane values ≤
      Subgroup.normalizer (core : Set GroupType) := by
  let core := signalizerHyperplaneCore prime rank groupPrime actor hyperplane values
  have complete := (locally_complete.2 groupPrime prime_member).1
  change core ≤ signalizerPrimeCompletion prime rank actor values
    (signalizerSpectrum prime rank actor values \ {groupPrime}) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · apply iSup_le
    intro selected
    apply iSup_le
    intro member
    apply iSup_le
    intro _
    exact signalizer_local_complement_core_le_prime_completion prime rank groupPrime prime_prime
      groupPrime_prime actor elementary large values conditions complete selected member
  · apply normalizer_biSup_of_le
    intro selected member
    apply normalizer_iSup_of_le
    intro _
    let _characteristic := prime_set_core_characteristic (GroupType := values selected) ({groupPrime}ᶜ)
    exact characteristic_subgroup_map_normalized actor (values selected)
      (conditions.normalized selected member) (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ))
  · apply normalizer_biSup_of_le
    intro selected member
    apply normalizer_iSup_of_le
    intro contained
    let _characteristic := prime_set_core_characteristic (GroupType := values selected) ({groupPrime}ᶜ)
    have fixed_le : signalizerHyperplaneCommonFixed prime rank actor hyperplane values ≤ values selected :=
      inf_le_right.trans (iInf_le_of_le selected (iInf_le_of_le member (iInf_le_of_le contained le_rfl)))
    exact characteristic_subgroup_map_normalized _ (values selected)
      (fixed_le.trans Subgroup.le_normalizer) (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ))

omit [Finite GroupType] in
theorem signalizer_compatible_hyperplane_fixed_le (prime rank : ℕ)
    (actor hyperplane target : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (compatible : signalizerCompatible prime rank actor values target) :
    target ⊓ Subgroup.centralizer (hyperplane : Set GroupType) ≤
      signalizerHyperplaneCommonFixed prime rank actor hyperplane values := by
  intro element member
  refine ⟨member.2, Subgroup.mem_iInf.mpr fun selected => Subgroup.mem_iInf.mpr fun selected_member =>
    Subgroup.mem_iInf.mpr fun contained => ?_⟩
  exact compatible.2 selected selected_member ⟨member.1, Subgroup.centralizer_le contained member.2⟩

omit [Finite GroupType] in
theorem elementary_hyperplane_rank_bound (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor hyperplane : Subgroup GroupType) (contained : hyperplane ≤ actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (hyperplane_index : (hyperplane.subgroupOf actor).index = prime) :
    prime ^ (rank + 1) ≤ Nat.card hyperplane := by
  have cardinality := (hyperplane.subgroupOf actor).card_mul_index
  rw [hyperplane_index, Nat.card_congr (Subgroup.subgroupOfEquivOfLe contained).toEquiv] at cardinality
  rw [← cardinality, show rank + 2 = (rank + 1) + 1 by omega, pow_succ] at large
  exact Nat.le_of_mul_le_mul_right large prime_prime.pos

end CFSG.SignalizerFunctor.Helpers
