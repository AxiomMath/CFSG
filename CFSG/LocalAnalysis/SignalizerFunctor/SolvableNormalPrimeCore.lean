module

public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem solvable_nontrivial_prime_core_exists [Group.IsSolvable GroupType] [Nontrivial GroupType] :
    ∃ prime : ℕ, prime.Prime ∧ prime ∣ Nat.card GroupType ∧ primeSetCore (GroupType := GroupType) {prime} ≠ ⊥ := by
  obtain ⟨normal, normal_property, normal_nontrivial, _, prime, rank, prime_prime, rank_positive, elementary, normal_card⟩ :=
    solvable_minimal_normal_exists (GroupType := GroupType)
  have prime_divides : prime ∣ Nat.card normal := by
    rw [normal_card]
    exact dvd_pow_self prime (by omega : rank ≠ 0)
  have supported := (prime_supported_singleton_iff_pgroup prime prime_prime normal).mpr
    (elementary_abelian_isPGroup prime normal elementary)
  have normal_core := prime_set_core_contains {prime} normal normal_property supported
  exact ⟨prime, prime_prime, prime_divides.trans (Subgroup.card_subgroup_dvd_card normal),
    fun trivial => normal_nontrivial (le_bot_iff.mp (normal_core.trans trivial.le))⟩

theorem pgroup_of_unique_prime_divisor (prime : ℕ) (prime_prime : prime.Prime)
    (unique : ∀ divisor : ℕ, divisor.Prime → divisor ∣ Nat.card GroupType → divisor = prime) : IsPGroup prime GroupType := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have cardinality := Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    (fun divisor_prime divides => unique _ divisor_prime divides)
  exact IsPGroup.iff_card.mpr ⟨(Nat.card GroupType).primeFactorsList.length, cardinality⟩

end CFSG.SignalizerFunctor.Helpers
