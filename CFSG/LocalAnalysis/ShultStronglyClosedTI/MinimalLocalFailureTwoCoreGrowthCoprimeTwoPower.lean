module

public import Mathlib.Algebra.Ring.GeomSum
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeFixedPoints

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

universe u

theorem two_pow_sub_one_dvd_iff_exponent_dvd
    (e d : ℕ) :
    (2 ^ e - 1) ∣ (2 ^ d - 1) ↔ e ∣ d := by
  constructor
  · intro h
    have hrem : 2 ^ (d % e) - 1 = 0 := by
      rw [← Nat.pow_sub_one_mod_pow_sub_one]
      exact Nat.mod_eq_zero_of_dvd h
    have hone : 2 ^ (d % e) = 1 := by
      have hpos := Nat.one_le_pow (d % e) 2 (by omega)
      omega
    have hzero : d % e = 0 := by
      rcases Nat.pow_eq_one.mp hone with htwo | hz
      · omega
      · exact hz
    exact Nat.dvd_of_mod_eq_zero hzero
  · exact Nat.pow_sub_one_dvd_pow_sub_one 2

theorem exponent_double_le_of_extra_prime_divisor
    {e d p : ℕ} (he : 0 < e) (hd : 0 < d)
    (hdiv : p * (2 ^ e - 1) ∣ 2 ^ d - 1) (hnot : ¬ p ∣ 2 ^ e - 1) :
    e ∣ d ∧ 2 * e ≤ d := by
  have hbase : 2 ^ e - 1 ∣ 2 ^ d - 1 := (dvd_mul_left _ p).trans hdiv
  have hexp : e ∣ d := (two_pow_sub_one_dvd_iff_exponent_dvd e d).mp hbase
  have hdne : d ≠ e := by
    intro h
    subst d
    exact hnot ((dvd_mul_right p _).trans hdiv)
  obtain ⟨k, hk⟩ := hexp
  have hk2 : 2 ≤ k := by
    by_contra hsmall
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · simp at hk
      omega
    · simp at hk
      exact hdne hk
  refine ⟨⟨k, hk⟩, ?_⟩
  rw [hk, mul_comm 2 e]
  exact mul_le_mul_of_nonneg_left hk2 he.le

theorem two_group_card_cube_le_of_extra_prime_divisor
    {M : Type u} [Group M] [Finite M] (hM : IsPGroup 2 M)
    (Q : Subgroup M) [Q.Normal] (hQproper : Q ≠ ⊤)
    {e p : ℕ} (he : 0 < e) (hQcard : Nat.card Q = 2 ^ e)
    (hdiv : p * (Nat.card Q - 1) ∣ Nat.card (M ⧸ Q) - 1)
    (hnot : ¬ p ∣ Nat.card Q - 1) :
    ∃ d : ℕ, Nat.card (M ⧸ Q) = 2 ^ d ∧ 0 < d ∧ e ∣ d ∧
      2 * e ≤ d ∧ Nat.card Q ^ 3 ≤ Nat.card M := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial (M ⧸ Q) := QuotientGroup.nontrivial_iff.mpr hQproper
  obtain ⟨d, hdcard⟩ := (hM.to_quotient Q).exists_card_eq
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hnontriv := Finite.one_lt_card (α := M ⧸ Q)
    simp [hd0] at hdcard
    omega
  obtain ⟨hexp, hdouble⟩ := exponent_double_le_of_extra_prime_divisor he hd
    (by simpa only [hQcard, hdcard] using hdiv)
    (by simpa only [hQcard] using hnot)
  refine ⟨d, hdcard, hd, hexp, hdouble, ?_⟩
  have hcard : Nat.card Q * Nat.card (M ⧸ Q) = Nat.card M := Q.card_mul_index
  rw [hQcard, hdcard, ← pow_add] at hcard
  rw [hQcard, ← hcard, ← pow_mul]
  apply (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mpr
  omega

theorem two_group_card_eq_cube_of_extra_prime_divisor_and_bound
    {M : Type u} [Group M] [Finite M] (hM : IsPGroup 2 M)
    (Q : Subgroup M) [Q.Normal] (hQproper : Q ≠ ⊤)
    {e p : ℕ} (he : 0 < e) (hQcard : Nat.card Q = 2 ^ e)
    (hdiv : p * (Nat.card Q - 1) ∣ Nat.card (M ⧸ Q) - 1)
    (hnot : ¬ p ∣ Nat.card Q - 1) (hbound : Nat.card M ∣ Nat.card Q ^ 3) :
    Nat.card M = Nat.card Q ^ 3 := by
  obtain ⟨d, hdcard, hd, hexp, hdouble, hlower⟩ :=
    two_group_card_cube_le_of_extra_prime_divisor hM Q hQproper he hQcard hdiv hnot
  exact le_antisymm (Nat.le_of_dvd (pow_pos (Nat.card_pos (α := Q)) 3) hbound) hlower

end CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime
