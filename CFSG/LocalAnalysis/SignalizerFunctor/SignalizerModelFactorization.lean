module

public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleFixedIntersections
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorizationTransfer
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageAmbientNormalizers

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem signalizer_normal_product_value_intersection
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor parent normal other : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ≤ Subgroup.centralizer (selected : Set GroupType))
    (parent_compatible : signalizerCompatible prime rank actor values parent)
    (normal_normalized : actor ≤ Subgroup.normalizer (normal : Set GroupType))
    (other_normalized : actor ≤ Subgroup.normalizer (other : Set GroupType))
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType))
    (other_coprime : Nat.Coprime prime (Nat.card other))
    (factorization : parent = normal ⊔ other)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    parent ⊓ values selected = (normal ⊓ values selected) ⊔ (other ⊓ values selected) := by
  have normal_le : normal ≤ parent := by rw [factorization]; exact le_sup_left
  have other_le : other ≤ parent := by rw [factorization]; exact le_sup_right
  have normal_compatible := signalizer_compatible_of_le prime rank actor values parent_compatible
    normal_le normal_normalized
  have other_compatible := signalizer_compatible_of_le prime rank actor values parent_compatible
    other_le other_normalized
  have formula := centralizer_sup_of_normalizing prime prime_prime selected normal other
    (elementary_abelian_isPGroup prime selected (elementary_abelian_of_le prime elementary member.1))
    (member.1.trans normal_normalized) (member.1.trans other_normalized) normalizes other_coprime
  rw [← factorization,
    signalizer_compatible_fixed_intersection prime rank actor parent values central parent_compatible
      selected member,
    signalizer_compatible_fixed_intersection prime rank actor normal values central normal_compatible
      selected member,
    signalizer_compatible_fixed_intersection prime rank actor other values central other_compatible
      selected member] at formula
  exact formula

theorem signalizer_two_stage_normalizer_completion_factorization
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor parent : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (parent_compatible : signalizerCompatible prime rank actor values parent)
    (sylow : Sylow groupPrime ((twoStageCore (GroupType := parent) groupPrime).map parent.subtype))
    (normalized : actor ≤ Subgroup.normalizer
      (((sylow : Subgroup ((twoStageCore (GroupType := parent) groupPrime).map parent.subtype)).map
        ((twoStageCore (GroupType := parent) groupPrime).map parent.subtype).subtype) : Set GroupType))
    (complete :
      let embedded := (sylow : Subgroup ((twoStageCore (GroupType := parent) groupPrime).map parent.subtype)).map
        ((twoStageCore (GroupType := parent) groupPrime).map parent.subtype).subtype
      signalizerCompatible prime rank actor values
        (signalizerNormalizerCompletion prime rank actor values embedded)) :
    let embedded := (sylow : Subgroup ((twoStageCore (GroupType := parent) groupPrime).map parent.subtype)).map
      ((twoStageCore (GroupType := parent) groupPrime).map parent.subtype).subtype
    parent = (primeSetCore (GroupType := parent) ({groupPrime}ᶜ)).map parent.subtype ⊔
      (signalizerNormalizerCompletion prime rank actor values embedded ⊓ parent) := by
  let embedded := (sylow : Subgroup ((twoStageCore (GroupType := parent) groupPrime).map parent.subtype)).map
    ((twoStageCore (GroupType := parent) groupPrime).map parent.subtype).subtype
  have embedded_le : embedded ≤ parent :=
    (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have compatible := signalizer_compatible_of_le prime rank actor values parent_compatible
    embedded_le normalized
  have intersection := signalizer_normalizer_completion_model_intersection prime rank prime_prime
    actor embedded parent elementary large values conditions compatible parent_compatible complete
  have formula := two_stage_ambient_sylow_normalizer_factorization groupPrime groupPrime_prime parent sylow
  rw [intersection] at formula
  exact formula

theorem signalizer_model_center_factorization
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor model : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (model_compatible : solvableSignalizerCompatible prime rank actor values model)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (sylow : Sylow groupPrime ((twoStageCore (GroupType := model) groupPrime).map model.subtype))
    (normalized : actor ≤ Subgroup.normalizer
      (((sylow : Subgroup ((twoStageCore (GroupType := model) groupPrime).map model.subtype)).map
        ((twoStageCore (GroupType := model) groupPrime).map model.subtype).subtype) : Set GroupType))
    (nontrivial : (sylow : Subgroup ((twoStageCore (GroupType := model) groupPrime).map model.subtype)).map
      ((twoStageCore (GroupType := model) groupPrime).map model.subtype).subtype ≠ ⊥) :
    let embedded := (sylow : Subgroup ((twoStageCore (GroupType := model) groupPrime).map model.subtype)).map
      ((twoStageCore (GroupType := model) groupPrime).map model.subtype).subtype
    let center := (Subgroup.center embedded).map embedded.subtype
    let localCompletion := signalizerNormalizerCompletion prime rank actor values center
    model = (primeSetCore (GroupType := model) ({groupPrime}ᶜ)).map model.subtype ⊔
      (localCompletion ⊓ model) ∧
    ∀ selected ∈ signalizerFunctorEk prime rank actor,
      model ⊓ values selected =
        ((primeSetCore (GroupType := model) ({groupPrime}ᶜ)).map model.subtype ⊓ values selected) ⊔
          ((localCompletion ⊓ model) ⊓ values selected) := by
  let embedded := (sylow : Subgroup ((twoStageCore (GroupType := model) groupPrime).map model.subtype)).map
    ((twoStageCore (GroupType := model) groupPrime).map model.subtype).subtype
  let center := (Subgroup.center embedded).map embedded.subtype
  let localCompletion := signalizerNormalizerCompletion prime rank actor values center
  let core := (primeSetCore (GroupType := model) ({groupPrime}ᶜ)).map model.subtype
  have properties := signalizer_factorization_auxiliary_center prime rank groupPrime groupPrime_prime
    actor model values model_compatible locally_complete sylow normalized nontrivial
  have intersection := signalizer_normalizer_completion_model_intersection prime rank prime_prime actor
    center model elementary large values conditions properties.2.2.2.1.1 model_compatible.1
    properties.2.2.2.2.1
  have formula := two_stage_ambient_sylow_center_normalizer_factorization groupPrime groupPrime_prime model sylow
  change model = core ⊔ (model ⊓ Subgroup.normalizer (center : Set GroupType)) at formula
  rw [intersection] at formula
  change model = core ⊔ (localCompletion ⊓ model) at formula
  change model = core ⊔ (localCompletion ⊓ model) ∧ _
  refine ⟨formula, ?_⟩
  let _characteristic := prime_set_core_characteristic (GroupType := model) ({groupPrime}ᶜ)
  have core_normalized := characteristic_subgroup_map_normalized actor model model_compatible.1.1
    (primeSetCore (GroupType := model) ({groupPrime}ᶜ))
  have model_normalizes_core := characteristic_subgroup_map_normalized model model Subgroup.le_normalizer
    (primeSetCore (GroupType := model) ({groupPrime}ᶜ))
  have other_normalized := normalizer_inf_of_le actor localCompletion model properties.2.2.2.2.1.1
    model_compatible.1.1
  have model_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    ((pow_le_pow_right' prime_prime.one_le (Nat.le_succ rank)).trans large) values conditions.coprime
    model model_compatible.1.1 model_compatible.1.2
  exact signalizer_normal_product_value_intersection prime rank prime_prime actor model core
    (localCompletion ⊓ model) elementary values conditions.central model_compatible.1 core_normalized
    other_normalized (inf_le_right.trans model_normalizes_core)
    (model_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_right)) formula

end CFSG.SignalizerFunctor.Helpers
