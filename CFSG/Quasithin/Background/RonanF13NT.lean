module

public import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.RonanF13

private theorem dvd_pow_sub_one_gcd {N x a b : ℕ} (ha : N ∣ x ^ a - 1) (hb : N ∣ x ^ b - 1) :
    N ∣ x ^ Nat.gcd a b - 1 := by
  rw [← Nat.pow_sub_one_gcd_pow_sub_one]
  exact Nat.dvd_gcd ha hb

private theorem t_eq_one {M c N g t : ℕ} (hM : 1 ≤ M) (hc : c = 1 ∨ c = 3)
    (hc3 : c = 3 → 4 ≤ M) (hcN : c * N = 2 ^ M - 1) (hg : 1 ≤ g)
    (hNle : N ≤ 2 ^ g - 1) (ht : M = g * t) : t = 1 := by
  by_contra hne
  have ht2 : 2 ≤ t := by
    by_contra h
    have h01 : t = 0 ∨ t = 1 := by omega
    rcases h01 with rfl | rfl
    · omega
    · exact hne rfl
  have hM2 : 2 * g ≤ M := by
    rw [ht]
    nlinarith
  have hpow2 : 2 ≤ 2 ^ g := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  rcases hc with rfl | rfl
  ·
    have h1M : 2 ^ (g + 1) ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsucc : 2 ^ (g + 1) = 2 * 2 ^ g := by ring
    omega
  ·
    have h4 : 4 ≤ M := hc3 rfl
    have hsq : 2 ^ g * 2 ^ g ≤ 2 ^ M := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h16 : 16 ≤ 2 ^ M := by
      calc (16:ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) h4
    have hP : 3 * N + 1 = 2 ^ M := by omega
    obtain ⟨y, hy⟩ : ∃ y, 2 ^ g = y := ⟨_, rfl⟩
    rw [hy] at hNle hsq hpow2
    have hNy : N + 1 ≤ y := by omega
    have hyle : y ≤ 2 := by
      by_contra hcon
      have hy3 : 3 ≤ y := by omega
      have h3y : 3 * y ≤ y * y := Nat.mul_le_mul_right y hy3
      omega
    omega

private theorem dvd_of_dvd_two_pow_sub_one {M c N s : ℕ} (hM : 1 ≤ M) (hc : c = 1 ∨ c = 3)
    (hc3 : c = 3 → 4 ≤ M) (hcN : c * N = 2 ^ M - 1) (hs : N ∣ 2 ^ s - 1) : M ∣ s := by
  have hNM : N ∣ 2 ^ M - 1 := by
    rw [← hcN]
    exact dvd_mul_left N c
  have hgpos : 0 < Nat.gcd M s := Nat.gcd_pos_of_pos_left s (by omega)
  have hNg : N ∣ 2 ^ Nat.gcd M s - 1 := dvd_pow_sub_one_gcd hNM hs
  have hpow2 : 2 ≤ 2 ^ Nat.gcd M s := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Nat.gcd M s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNle : N ≤ 2 ^ Nat.gcd M s - 1 := Nat.le_of_dvd (by omega) hNg
  obtain ⟨t, ht⟩ := Nat.gcd_dvd_left M s
  have ht1 : t = 1 := t_eq_one hM hc hc3 hcN (by omega) hNle ht
  rw [ht1, mul_one] at ht
  rw [ht]
  exact Nat.gcd_dvd_right M s

theorem nt_main {M c N k r : ℕ} (hM : 1 ≤ M) (hc : c = 1 ∨ c = 3) (hc3 : c = 3 → 4 ≤ M)
    (hcN : c * N = 2 ^ M - 1) (h1 : N ∣ (2 ^ k - 1) ^ 2) (hr : Odd r)
    (h2 : N ∣ 2 ^ (k * r) - 1) : N ∣ 2 ^ k - 1 := by
  have hMdvd : M ∣ k * r := dvd_of_dvd_two_pow_sub_one hM hc hc3 hcN h2
  obtain ⟨g, r0, j, hgpos, hcop, hM0, hk0⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_left k (by omega : 0 < M))
  subst hM0 hk0
  have hr0r : r0 ∣ r := by
    have h' : r0 * g ∣ j * r * g := by
      have e : j * r * g = j * g * r := by ring
      rw [e]
      exact hMdvd
    exact hcop.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_right hgpos).mp h')
  have hro : Odd r0 := Odd.of_dvd_nat hr hr0r
  by_cases hr01 : r0 = 1
  ·
    subst hr01
    have hNM : N ∣ 2 ^ (1 * g) - 1 := by
      rw [← hcN]
      exact dvd_mul_left N c
    have hdvd : 2 ^ (1 * g) - 1 ∣ 2 ^ (j * g) - 1 := by
      have hMk : 1 * g ∣ j * g := by
        rw [one_mul]
        exact dvd_mul_left g j
      have hgcd : Nat.gcd (j * g) (1 * g) = 1 * g := Nat.gcd_eq_right hMk
      have h3 := Nat.gcd_dvd_left (2 ^ (j * g) - 1) (2 ^ (1 * g) - 1)
      rw [Nat.pow_sub_one_gcd_pow_sub_one, hgcd] at h3
      exact h3
    exact hNM.trans hdvd
  ·
    exfalso
    have hr03 : 3 ≤ r0 := by
      obtain ⟨m, hm⟩ := hro
      omega
    have hpow2 : 2 ≤ 2 ^ g := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨b, hb⟩ : ∃ b, 2 ^ g = b + 1 := ⟨2 ^ g - 1, by omega⟩
    have hb1 : 1 ≤ b := by omega
    have hMpow : 2 ^ (r0 * g) = (b + 1) ^ r0 := by
      rw [mul_comm r0 g, pow_mul, hb]
    have hkpow : 2 ^ (j * g) = (b + 1) ^ j := by
      rw [mul_comm j g, pow_mul, hb]
    have hN1 : N ∣ (b + 1) ^ r0 - 1 := by
      rw [← hMpow, ← hcN]
      exact dvd_mul_left N c
    have hN2 : N ∣ ((b + 1) ^ j - 1) * ((b + 1) ^ j - 1) := by
      rw [← pow_two, ← hkpow]
      exact h1
    have hgcd1 : Nat.gcd ((b + 1) ^ r0 - 1) ((b + 1) ^ j - 1) = b := by
      rw [Nat.pow_sub_one_gcd_pow_sub_one, hcop.gcd_eq_one, pow_one, Nat.add_sub_cancel]
    have hNb : N ∣ b * b := by
      have hG : Nat.gcd ((b + 1) ^ r0 - 1) (((b + 1) ^ j - 1) * ((b + 1) ^ j - 1)) ∣
          Nat.gcd ((b + 1) ^ r0 - 1) ((b + 1) ^ j - 1) *
            Nat.gcd ((b + 1) ^ r0 - 1) ((b + 1) ^ j - 1) :=
        gcd_mul_dvd_mul_gcd _ _ _
      rw [hgcd1] at hG
      exact (Nat.dvd_gcd hN1 hN2).trans hG
    have hNle2 : N ≤ b * b := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hNb
    have hcle : c * N ≤ 3 * N := by
      rcases hc with rfl | rfl <;> omega
    have hPow : c * N + 1 = (b + 1) ^ r0 := by
      have hpos : 0 < (b + 1) ^ r0 := by positivity
      rw [hMpow] at hcN
      omega
    have h3 : (b + 1) ^ 3 ≤ (b + 1) ^ r0 := Nat.pow_le_pow_right (by omega) hr03
    have hfin : (b + 1) ^ 3 ≤ 3 * (b * b) + 1 := by omega
    have key : (b + 1) ^ 3 = b * b * b + 3 * (b * b) + 3 * b + 1 := by ring
    omega

end CFSG.Quasithin.RonanF13
