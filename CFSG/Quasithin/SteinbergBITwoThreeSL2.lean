module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.Quasithin.SteinbergBI

open Matrix

variable {K : Type*} [Field K]

theorem range_le_of_transvection_mem {G : Type*} [Group G]
    (φ : SpecialLinearGroup (Fin 2) K →* G) (M : Subgroup G)
    (h01 : ∀ c : K, φ (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c) ∈ M)
    (h10 : ∀ c : K, φ (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c) ∈ M) :
    φ.range ≤ M := by
  rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, j, hij, c, rfl⟩, rfl⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01 c
  · exact h10 c
  · exact absurd rfl hij

theorem not_dvd_two_pow_mul_three_pow {q : ℕ} (hq2 : 2 ∣ q) (hq4 : 4 ≤ q) (a b : ℕ) :
    ¬q * (q ^ 2 - 1) ∣ 2 ^ a * 3 ^ b := by
  intro h
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring
  have hthree : ∀ d : ℕ, d ∣ q ^ 2 - 1 → ¬2 ∣ d → 3 ≤ d → 3 ∣ d := by
    intro d hd hd2 hd3
    have hd' : d ∣ 2 ^ a * 3 ^ b := (hd.trans (Dvd.intro_left q rfl)).trans h
    have hcop : Nat.Coprime d (2 ^ a) :=
      Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hd2).symm
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (hcop.dvd_of_dvd_mul_left hd')
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · omega
    · rw [hi]
      exact dvd_pow_self 3 hi0.ne'
  have h1 := hthree (q - 1) (by rw [hsq]; exact Dvd.intro _ rfl) (by omega) (by omega)
  have h2 := hthree (q + 1) (by rw [hsq]; exact Dvd.intro_left _ rfl) (by omega) (by omega)
  omega

theorem two_dvd_natCard [Finite K] [CharP K 2] : 2 ∣ Nat.card K := by
  let := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact (CharP.cast_eq_zero_iff K 2 _).1 (FiniteField.cast_card_eq_zero K)

theorem not_range_le_of_card_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) {G : Type*}
    [Group G] {φ : SpecialLinearGroup (Fin 2) K →* G} (hφ : Function.Injective φ)
    {M : Subgroup G} {a b : ℕ} (hM : Nat.card M = 2 ^ a * 3 ^ b) : ¬φ.range ≤ M := by
  intro hle
  have h := Subgroup.card_dvd_of_le hle
  rw [hM, ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv,
    CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two] at h
  exact not_dvd_two_pow_mul_three_pow two_dvd_natCard hq a b h

end CFSG.Quasithin.SteinbergBI
