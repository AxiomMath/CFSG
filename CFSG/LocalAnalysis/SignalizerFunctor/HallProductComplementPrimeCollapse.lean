module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductNormalPrimeCoreContradiction
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableNormalPrimeCore

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_complement_prime_collapse
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (complement_eq : complement = signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime})) :
    complement = ⊥ ∨ ∃ complementPrime : ℕ, complementPrime.Prime ∧ complementPrime ≠ groupPrime ∧
      IsPGroup complementPrime complement := by
  classical
  by_cases trivial : complement = ⊥
  · exact Or.inl trivial
  · let := datum.complement_compatible.2
    let : Nontrivial complement := (Subgroup.nontrivial_iff_ne_bot complement).mpr trivial
    obtain ⟨complementPrime, complementPrime_prime, complementPrime_divides, core_nontrivial⟩ :=
      solvable_nontrivial_prime_core_exists (GroupType := complement)
    have distinct : complementPrime ≠ groupPrime := fun same => datum.groupPrime_prime.coprime_iff_not_dvd.mp
      datum.complement_coprime (same ▸ complementPrime_divides)
    have unique : ∀ divisor : ℕ, divisor.Prime → divisor ∣ Nat.card complement → divisor = complementPrime := by
      intro divisor divisor_prime divides
      by_contra different
      exact incomplete_abelian_hall_product_prime_core_contradiction datum abelian large common_le_parent complement_eq
        complementPrime divisor complementPrime_prime divisor_prime core_nontrivial divides different
    exact Or.inr ⟨complementPrime, complementPrime_prime, distinct,
      pgroup_of_unique_prime_divisor complementPrime complementPrime_prime unique⟩

theorem incomplete_hall_product_complement_nontrivial
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values) : complement ≠ ⊥ := by
  intro trivial
  have parent_equal : parent = factor := by
    apply SetLike.coe_injective
    rw [← datum.whole, trivial]
    ext element
    constructor
    · rintro ⟨first, first_member, second, second_member, product⟩
      have identity : first = 1 := first_member
      change first * second = element at product
      rw [identity, one_mul] at product
      rwa [← product]
    · intro member
      exact ⟨1, Subgroup.one_mem _, element, member, one_mul element⟩
  have solvable : Group.IsSolvable factor := by
    let : Fact groupPrime.Prime := ⟨datum.groupPrime_prime⟩
    let _nilpotent := datum.factor_pgroup.isNilpotent
    infer_instance
  exact datum.incomplete (parent_equal ▸ ⟨datum.factor_compatible, solvable⟩)

theorem incomplete_abelian_hall_product_complement_pgroup
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (complement_eq : complement = signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime})) :
    ∃ complementPrime : ℕ, complementPrime.Prime ∧ complementPrime ≠ groupPrime ∧ IsPGroup complementPrime complement := by
  rcases incomplete_abelian_hall_product_complement_prime_collapse datum abelian large common_le_parent complement_eq
    with trivial | pgroup
  · exact (incomplete_hall_product_complement_nontrivial datum trivial).elim
  · exact pgroup

end CFSG.SignalizerFunctor.Helpers
