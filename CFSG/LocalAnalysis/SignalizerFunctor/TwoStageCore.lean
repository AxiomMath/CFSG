module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSetCore

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem prime_supported_singleton_iff_pgroup (prime : ℕ) (prime_prime : prime.Prime)
    (target : Subgroup GroupType) :
    primeSupported {prime} (Nat.card target) ↔ IsPGroup prime target := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  constructor
  · intro supported
    apply IsPGroup.of_card
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro divisor divisor_prime divides
    exact supported divisor divisor_prime divides
  · intro pgroup
    obtain ⟨rank, cardinality⟩ := pgroup.exists_card_eq
    rw [cardinality]
    exact prime_supported_pow_prime {prime} prime rank prime_prime rfl

theorem prime_supported_complement_singleton_iff_coprime (prime : ℕ) (prime_prime : prime.Prime)
    (order : ℕ) : primeSupported ({prime}ᶜ) order ↔ Nat.Coprime prime order := by
  constructor
  · intro supported
    apply prime_prime.coprime_iff_not_dvd.mpr
    intro divides
    exact supported prime prime_prime divides rfl
  · intro coprime divisor divisor_prime divides member
    have equality : divisor = prime := member
    subst divisor
    exact prime_prime.coprime_iff_not_dvd.mp coprime divides

theorem prime_core_isPGroup (prime : ℕ) (prime_prime : prime.Prime) :
    IsPGroup prime (primeSetCore (GroupType := GroupType) {prime}) :=
  (prime_supported_singleton_iff_pgroup prime prime_prime _).mp (prime_set_core_supported {prime})

theorem solvable_prime_core_nontrivial_of_complement_core_trivial
    [Group.IsSolvable GroupType] [Nontrivial GroupType]
    (prime : ℕ) (prime_prime : prime.Prime)
    (complement_trivial : primeSetCore (GroupType := GroupType) ({prime}ᶜ) = ⊥) :
    primeSetCore (GroupType := GroupType) {prime} ≠ ⊥ := by
  obtain ⟨minimal, normal, nontrivial, _, divisor, rank, divisor_prime, _, _, cardinality⟩ :=
    solvable_minimal_normal_exists (GroupType := GroupType)
  have same_prime : divisor = prime := by
    by_contra distinct
    have complement_supported : primeSupported ({prime}ᶜ) (Nat.card minimal) := by
      rw [cardinality]
      exact prime_supported_pow_prime ({prime}ᶜ) divisor rank divisor_prime
        (by intro equal; exact distinct equal)
    have contained := prime_set_core_contains ({prime}ᶜ) minimal normal complement_supported
    rw [complement_trivial] at contained
    exact nontrivial (le_bot_iff.mp contained)
  have minimal_supported : primeSupported {prime} (Nat.card minimal) := by
    rw [cardinality, same_prime]
    exact prime_supported_pow_prime {prime} prime rank prime_prime rfl
  have contained := prime_set_core_contains {prime} minimal normal minimal_supported
  intro trivial
  rw [trivial] at contained
  exact nontrivial (le_bot_iff.mp contained)

@[expose] def twoStageCore (prime : ℕ) : Subgroup GroupType :=
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  (primeSetCore (GroupType := GroupType ⧸ complement) {prime}).comap (QuotientGroup.mk' complement)

omit [Finite GroupType] in
theorem two_stage_core_normal (prime : ℕ) : (twoStageCore (GroupType := GroupType) prime).Normal := by
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  let _quotientNormal := prime_set_core_normal (GroupType := GroupType ⧸ complement) {prime}
  change ((primeSetCore (GroupType := GroupType ⧸ complement) {prime}).comap
    (QuotientGroup.mk' complement)).Normal
  exact inferInstance

theorem two_stage_core_characteristic (prime : ℕ) :
    (twoStageCore (GroupType := GroupType) prime).Characteristic := by
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _characteristic := prime_set_core_characteristic (GroupType := GroupType) ({prime}ᶜ)
  let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  change ((primeSetCore (GroupType := GroupType ⧸ complement) {prime}).comap
    (QuotientGroup.mk' complement)).Characteristic
  exact Subgroup.Characteristic.comap_quotient_mk (H := complement)
    (prime_set_core_characteristic (GroupType := GroupType ⧸ complement) {prime})

theorem two_stage_core_has_prime_part [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (divides : prime ∣ Nat.card GroupType) :
    prime ∣ Nat.card (twoStageCore (GroupType := GroupType) prime) := by
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  have complement_coprime := (prime_supported_complement_singleton_iff_coprime prime prime_prime
    (Nat.card complement)).mp (prime_set_core_supported (GroupType := GroupType) ({prime}ᶜ))
  have quotient_divides : prime ∣ Nat.card (GroupType ⧸ complement) := by
    have card_formula := complement.card_mul_index
    rw [Subgroup.index_eq_card] at card_formula
    rw [← card_formula] at divides
    exact complement_coprime.dvd_of_dvd_mul_left divides
  have quotient_card_not_one : Nat.card (GroupType ⧸ complement) ≠ 1 := by
    intro equal
    rw [equal] at quotient_divides
    exact prime_prime.not_dvd_one quotient_divides
  let _quotientNontrivial : Nontrivial (GroupType ⧸ complement) :=
    Finite.one_lt_card_iff_nontrivial.mp (by have := Nat.card_pos (α := GroupType ⧸ complement); omega)
  have quotient_core_nontrivial := solvable_prime_core_nontrivial_of_complement_core_trivial
    (GroupType := GroupType ⧸ complement) prime prime_prime (prime_set_core_quotient_trivial ({prime}ᶜ))
  let : Fact prime.Prime := ⟨prime_prime⟩
  have core_divides : prime ∣ Nat.card (primeSetCore (GroupType := GroupType ⧸ complement) {prime}) := by
    rcases (prime_core_isPGroup (GroupType := GroupType ⧸ complement) prime prime_prime).card_eq_or_dvd
      with cardinality | divides
    · exact (quotient_core_nontrivial ((Subgroup.eq_bot_iff_card _).mpr cardinality)).elim
    · exact divides
  have mapped_eq : (twoStageCore (GroupType := GroupType) prime).map (QuotientGroup.mk' complement) =
      primeSetCore (GroupType := GroupType ⧸ complement) {prime} :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective complement) _
  rw [← mapped_eq] at core_divides
  exact core_divides.trans (Subgroup.card_map_dvd _ _)

end CFSG.SignalizerFunctor.Helpers
