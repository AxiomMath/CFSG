module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerLocalValueFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorizationClosure

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem signalizer_normalizer_factorization_complete
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor model : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (model_compatible : solvableSignalizerCompatible prime rank actor values model)
    (factorization : signalizerNormalizerFactorization prime rank groupPrime actor values model) :
    solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) := by
  have generation_large : prime ^ (rank + 1) ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (by omega : rank + 1 ≤ rank + 2)).trans large
  obtain ⟨sylow, normalized, nontrivial⟩ := signalizer_factorization_invariant_sylow_exists prime rank
    groupPrime prime_prime groupPrime_prime actor model elementary generation_large values conditions
    locally_complete prime_member model_compatible factorization
  let embedded := (sylow : Subgroup ((twoStageCore (GroupType := model) groupPrime).map model.subtype)).map
    ((twoStageCore (GroupType := model) groupPrime).map model.subtype).subtype
  let center := (Subgroup.center embedded).map embedded.subtype
  let source := signalizerNormalizerCompletion prime rank actor values center
  have properties := signalizer_factorization_auxiliary_center prime rank groupPrime groupPrime_prime actor
    model values model_compatible locally_complete sylow normalized nontrivial
  have model_factorization := signalizer_model_center_factorization prime rank groupPrime prime_prime
    groupPrime_prime actor model elementary generation_large values conditions model_compatible locally_complete
    sylow normalized nontrivial
  have source_normalizes : source ≤ Subgroup.normalizer (center : Set GroupType) :=
    iSup_le fun _ => iSup_le fun _ => inf_le_right
  have local_factorization := signalizer_local_value_factorization prime rank groupPrime prime_prime
    groupPrime_prime actor source model elementary generation_large values conditions locally_complete
    properties.2.2.2.2 model_compatible model_factorization.1 factorization
  exact signalizer_local_factorization_complete prime rank groupPrime prime_prime groupPrime_prime actor source
    center elementary large values conditions locally_complete prime_member properties.2.2.2.2.1
    properties.2.2.2.1.1 properties.2.2.1 properties.2.1 properties.1 source_normalizes local_factorization

end CFSG.SignalizerFunctor.Helpers
