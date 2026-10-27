module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerHyperplaneSplitting
public import CFSG.LocalAnalysis.SignalizerFunctor.PermutingSubgroupProducts
public import CFSG.LocalAnalysis.SignalizerFunctor.HyperplaneGeneration

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

@[expose] def signalizerHyperplanes (prime : ℕ) (actor : Subgroup GroupType) :=
  {hyperplane : Subgroup GroupType // hyperplane ≤ actor ∧ (hyperplane.subgroupOf actor).index = prime}

theorem hyperplane_generation_subtype (prime : ℕ) (prime_prime : prime.Prime)
    (actor target : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (actor_nontrivial : actor ≠ ⊥) (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) :
    (⨆ hyperplane : signalizerHyperplanes prime actor,
      target ⊓ Subgroup.centralizer (hyperplane.val : Set GroupType)) = target := by
  have generation := elementary_abelian_hyperplane_generation prime prime_prime actor target elementary
    actor_nontrivial normalized coprime
  apply le_antisymm (iSup_le fun _ => inf_le_left)
  conv_lhs => rw [← generation]
  apply iSup_le
  intro hyperplane
  apply iSup_le
  intro contained
  apply iSup_le
  intro index_eq
  exact le_iSup_of_le (⟨hyperplane, contained, index_eq⟩ : signalizerHyperplanes prime actor) le_rfl

omit [Finite GroupType] in
theorem coprime_sup_of_permuting_product (prime : ℕ) (prime_prime : prime.Prime)
    (first second : Subgroup GroupType)
    (first_coprime : Nat.Coprime prime (Nat.card first))
    (second_coprime : Nat.Coprime prime (Nat.card second))
    (product_eq : subgroupProduct first second = ((first ⊔ second : Subgroup GroupType) : Set GroupType)) :
    Nat.Coprime prime (Nat.card (first ⊔ second : Subgroup GroupType)) := by
  apply prime_prime.coprime_iff_not_dvd.mpr
  intro divides
  have cardinality := subgroup_product_cardinality first second
  rw [product_eq] at cardinality
  have product_divides : prime ∣ Nat.card first * Nat.card second := by
    rw [cardinality]
    exact dvd_mul_of_dvd_left divides _
  exact (prime_prime.not_dvd_mul (prime_prime.coprime_iff_not_dvd.mp first_coprime)
    (prime_prime.coprime_iff_not_dvd.mp second_coprime)) product_divides

theorem signalizer_auxiliary_product
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor source auxiliary : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (source_normalized : actor ≤ Subgroup.normalizer (source : Set GroupType))
    (auxiliary_compatible : signalizerCompatible prime rank actor values auxiliary)
    (source_normalizes_auxiliary : source ≤ Subgroup.normalizer (auxiliary : Set GroupType))
    (local_factorization : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected =
        (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
          (values selected ⊓ source)) :
    let completion := signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime})
    subgroupProduct completion auxiliary = ((completion ⊔ auxiliary : Subgroup GroupType) : Set GroupType) ∧
      subgroupProduct auxiliary completion = subgroupProduct completion auxiliary ∧
      Nat.Coprime prime (Nat.card (completion ⊔ auxiliary : Subgroup GroupType)) ∧
      actor ≤ Subgroup.normalizer ((completion ⊔ auxiliary : Subgroup GroupType) : Set GroupType) := by
  let completion := signalizerPrimeCompletion prime rank actor values
    (signalizerSpectrum prime rank actor values \ {groupPrime})
  have rank_bound : prime ^ (rank + 1) ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (by omega : rank + 1 ≤ rank + 2)).trans large
  have actor_nontrivial : actor ≠ ⊥ := by
    intro trivial
    have actor_card := (Subgroup.eq_bot_iff_card actor).mp trivial
    rw [actor_card] at large
    have lower : prime ≤ prime ^ (rank + 2) := by
      simpa only [pow_one] using pow_le_pow_right' prime_prime.one_le (by omega : 1 ≤ rank + 2)
    have bound := lower.trans large
    have prime_large := prime_prime.two_le
    omega
  have prime_complete := (locally_complete.2 groupPrime prime_member).1
  have control := signalizer_prime_completion_control prime rank prime_prime actor elementary rank_bound
    values conditions (signalizerSpectrum prime rank actor values \ {groupPrime}) prime_complete
  have rank_lower : prime ^ rank ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (Nat.le_succ rank)).trans rank_bound
  have completion_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary rank_lower
    values conditions.coprime completion control.1.1 control.1.2
  have auxiliary_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary rank_lower
    values conditions.coprime auxiliary auxiliary_compatible.1 auxiliary_compatible.2
  let localFactors := fun hyperplane : signalizerHyperplanes prime actor =>
    auxiliary ⊓ Subgroup.centralizer (hyperplane.val : Set GroupType)
  let localCores := fun hyperplane : signalizerHyperplanes prime actor =>
    signalizerHyperplaneCore prime rank groupPrime actor hyperplane.val values
  have generation := hyperplane_generation_subtype prime prime_prime actor auxiliary elementary actor_nontrivial
    auxiliary_compatible.1 auxiliary_coprime
  have cores_properties := fun hyperplane : signalizerHyperplanes prime actor =>
    signalizer_hyperplane_core_properties prime rank groupPrime prime_prime groupPrime_prime actor hyperplane.val
      elementary rank_bound values conditions locally_complete prime_member
  have local_normalizes : ∀ hyperplane : signalizerHyperplanes prime actor,
      localFactors hyperplane ≤ Subgroup.normalizer (localCores hyperplane : Set GroupType) := by
    intro hyperplane
    exact (signalizer_compatible_hyperplane_fixed_le prime rank actor hyperplane.val auxiliary values
      auxiliary_compatible).trans (cores_properties hyperplane).2.2
  have splitting : ∀ hyperplane : signalizerHyperplanes prime actor,
      subgroupProduct (localCores hyperplane) (completion ⊓ source) = (completion : Set GroupType) := by
    intro hyperplane
    exact signalizer_hyperplane_core_splitting prime rank groupPrime prime_prime groupPrime_prime actor hyperplane.val
      source elementary large hyperplane.property.1 hyperplane.property.2 values conditions locally_complete
      prime_member source_normalized local_factorization
  have product := generated_local_factors_product_eq_sup completion auxiliary (completion ⊓ source)
    localFactors localCores generation (fun _ => inf_le_left) (fun hyperplane => (cores_properties hyperplane).1)
    inf_le_left local_normalizes (inf_le_right.trans source_normalizes_auxiliary) splitting
  change subgroupProduct completion auxiliary = ((completion ⊔ auxiliary : Subgroup GroupType) : Set GroupType) ∧
    subgroupProduct auxiliary completion = subgroupProduct completion auxiliary ∧ _
  exact ⟨product.1, product.2,
    coprime_sup_of_permuting_product prime prime_prime completion auxiliary completion_coprime auxiliary_coprime product.1,
    (le_inf control.1.1 auxiliary_compatible.1).trans
      (Subgroup.inf_normalizer_le_normalizer_sup completion auxiliary)⟩

end CFSG.SignalizerFunctor.Helpers
