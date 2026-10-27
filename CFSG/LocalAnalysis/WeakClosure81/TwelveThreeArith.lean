module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem b12_TwelveThreeArith_exists_mul {n k : ℕ} (hk : 1 ≤ k) (hkn : k ∣ n)
    (hlt : k < n) : ∃ j : ℕ, n = k * j ∧ 2 ≤ j := by
  obtain ⟨j, rfl⟩ := hkn
  refine ⟨j, rfl, ?_⟩
  by_contra hj
  have hj' : j ≤ 1 := by omega
  have : k * j ≤ k * 1 := Nat.mul_le_mul_left k hj'
  omega

private theorem b12_TwelveThreeArith_odd {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
  exact ⟨2 ^ (n - 1) - 1, by omega⟩

theorem eq_two_mul_of_two_pow_sub_one_dvd_card_psl {n k : ℕ} (hk : 1 ≤ k) (hkn : k ∣ n)
    (hlt : k < n) (hdvd : (2 ^ n - 1) ∣ (2 ^ k + 1) * 2 ^ k * (2 ^ k - 1)) : n = 2 * k := by
  obtain ⟨j, hnj, hj2⟩ := b12_TwelveThreeArith_exists_mul hk hkn hlt
  have hk2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨b, hb⟩ : ∃ b : ℕ, 2 ^ k = b + 1 := ⟨2 ^ k - 1, by omega⟩
  have hb1 : 1 ≤ b := by omega
  have hodd : Odd (2 ^ n - 1) := b12_TwelveThreeArith_odd (by omega)
  have hcop : Nat.Coprime (2 ^ n - 1) (2 ^ k) :=
    Nat.Coprime.pow_right k hodd.coprime_two_right
  have h1 : (2 ^ k + 1) * 2 ^ k * (2 ^ k - 1) = 2 ^ k * ((2 ^ k + 1) * (2 ^ k - 1)) := by ring
  rw [h1] at hdvd
  have hdvd' : (2 ^ n - 1) ∣ (2 ^ k + 1) * (2 ^ k - 1) := hcop.dvd_of_dvd_mul_left hdvd
  rw [hb] at hdvd'
  have hM : (b + 1 + 1) * (b + 1 - 1) = (b + 2) * b := by simp
  rw [hM] at hdvd'
  have hMpos : 0 < (b + 2) * b := by positivity
  have hle := Nat.le_of_dvd hMpos hdvd'
  by_contra hne
  have hj3 : 3 ≤ j := by
    by_contra hj
    have : j = 2 := by omega
    exact hne (by rw [hnj, this]; ring)
  have h3 : (b + 1) ^ 3 ≤ 2 ^ n := by
    rw [← hb, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [hnj]; nlinarith)
  have hcube : (b + 1) ^ 3 - 1 = b ^ 3 + 3 * b ^ 2 + 3 * b :=
    Nat.sub_eq_of_eq_add (by ring)
  have h8 : (b + 1) ^ 3 - 1 ≤ 2 ^ n - 1 := Nat.sub_le_sub_right h3 1
  rw [hcube] at h8
  nlinarith

theorem eq_of_mul_eq_two_pow_sub_one {n m k x : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hn : n = 2 * k)
    (hx : x * (2 ^ m - 1) = 2 ^ n - 1) (hxd : x ∣ 2 ^ k - 1 ∨ x ∣ 2 ^ k + 1) : m = k := by
  have hm2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨c, hc⟩ : ∃ c : ℕ, 2 ^ m = c + 1 := ⟨2 ^ m - 1, by omega⟩
  have hk2 : 2 ≤ 2 ^ k := by
    calc 2 ≤ 2 ^ m := hm2
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hmk
  obtain ⟨b, hb⟩ : ∃ b : ℕ, 2 ^ k = b + 1 := ⟨2 ^ k - 1, by omega⟩
  have hcb : c ≤ b := by
    have : 2 ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hmk
    omega
  have hb1 : 1 ≤ b := by omega
  have hn' : 2 ^ n = (b + 1) ^ 2 := by rw [hn, pow_mul', hb]
  have hx' : x * c = b * (b + 2) := by
    rw [hc, hn'] at hx
    have h1 : b * (b + 2) = (b + 1) ^ 2 - 1 := (Nat.sub_eq_of_eq_add (by ring)).symm
    rw [h1, ← hx]
    simp
  rcases hxd with hxd | hxd
  · rw [hb] at hxd
    have hxb : x ≤ b := Nat.le_of_dvd (by omega) (by simpa using hxd)
    nlinarith
  · rw [hb] at hxd
    have hxb : x ≤ b + 2 := Nat.le_of_dvd (by omega) (by simpa [add_assoc] using hxd)
    have hbc : b ≤ c := by nlinarith
    have heq : 2 ^ m = 2 ^ k := by omega
    exact Nat.pow_right_injective (le_refl 2) heq

end CFSG.LocalAnalysis.WeakClosure81
