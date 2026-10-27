module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.H13.P31X

theorem l3_odd_of_three_dvd_two_pow_add_one {j : ℕ} (h : 3 ∣ 2 ^ j + 1) : Odd j := by
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | hodd
  · exfalso
    subst hk
    have h4 : (2 : ℕ) ^ (k + k) = 4 ^ k := by
      rw [← two_mul, pow_mul]
      norm_num
    have hmod : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [h4] at h
    omega
  · exact hodd

theorem l3_not_dvd_two_pow_sub_one {n p j : ℕ} (hn : Even n) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ 2 ^ (n / 2) + 1) (hj : Odd j) : ¬ p ∣ 2 ^ j - 1 := by
  intro hdiv
  obtain ⟨m, rfl⟩ := hn
  have hnm : (m + m) / 2 = m := by omega
  rw [hnm] at hpn
  have hjodd : j % 2 = 1 := Nat.odd_iff.mp hj
  have hA : ((2 ^ m + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpn
  have h1j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hB : ((2 ^ j - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  rw [Nat.cast_sub h1j] at hB
  push_cast at hA hB
  have hm1 : (2 : ZMod p) ^ m = -1 := by linear_combination hA
  have hj1 : (2 : ZMod p) ^ j = 1 := by linear_combination hB
  have hn2 : (2 : ZMod p) ^ (m + m) = 1 := by
    rw [pow_add, hm1]
    ring
  have hg : (2 : ZMod p) ^ Nat.gcd j (m + m) = 1 := pow_gcd_eq_one.2 ⟨hj1, hn2⟩
  have hg2 : ¬ 2 ∣ Nat.gcd j (m + m) := by
    intro h2
    have h2j : 2 ∣ j := dvd_trans h2 (Nat.gcd_dvd_left j (m + m))
    omega
  have hcop : Nat.Coprime (Nat.gcd j (m + m)) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hg2).symm
  have hgdvd : Nat.gcd j (m + m) ∣ 2 * m := by
    rw [two_mul]
    exact Nat.gcd_dvd_right j (m + m)
  obtain ⟨c, hc⟩ := Nat.Coprime.dvd_of_dvd_mul_left hcop hgdvd
  have hm_one : (2 : ZMod p) ^ m = 1 := by
    rw [hc, pow_mul, hg, one_pow]
  have h2zero : (2 : ZMod p) = 0 := by linear_combination hm1 - hm_one
  have h2cast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2zero
  have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp h2cast
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
  omega

theorem l3_exists_orderOf_eq_prime {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : Even n) (hp : p.Prime) (hpn : p ∣ 2 ^ (n / 2) + 1) :
    ∃ a : Kˣ, orderOf a = p := by
  haveI := Fact.mk hp
  haveI : Finite Kˣ := Finite.of_injective (Units.val : Kˣ → K) (fun _ _ h => Units.ext h)
  obtain ⟨m, rfl⟩ := hn
  have hnm : (m + m) / 2 = m := by omega
  rw [hnm] at hpn
  have hA : ((2 ^ m + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpn
  push_cast at hA
  have hm1 : (2 : ZMod p) ^ m = -1 := by linear_combination hA
  have h1 : 1 ≤ 2 ^ (m + m) := Nat.one_le_two_pow
  have hC : ((2 ^ (m + m) - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub h1]
    push_cast
    rw [pow_add, hm1]
    ring
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact (ZMod.natCast_eq_zero_iff _ _).mp hC
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hdvd
  exact ⟨a, ha⟩

end CFSG.Quasithin.H13.P31X
