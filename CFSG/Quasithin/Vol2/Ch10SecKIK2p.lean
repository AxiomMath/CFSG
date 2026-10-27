module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint

theorem key3D4 {x : ℕ} (hx : 2 ≤ x) :
    (x ^ 8 + x ^ 4 + 1) * (x ^ 6 - 1) * (x ^ 2 - 1) < (x ^ 12 - 1) * (x ^ 4 - 1) := by
  have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ x ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ x ^ 12 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h4]
  have hX : (2 : ℤ) ≤ x := by exact_mod_cast hx
  have key : ((x : ℤ) ^ 12 - 1) * ((x : ℤ) ^ 4 - 1) -
      ((x : ℤ) ^ 8 + (x : ℤ) ^ 4 + 1) * ((x : ℤ) ^ 6 - 1) * ((x : ℤ) ^ 2 - 1) =
      ((x : ℤ) ^ 8 + (x : ℤ) ^ 4 + 1) * ((x : ℤ) ^ 2 * ((x : ℤ) ^ 2 - 1) ^ 2) := by ring
  have hpos : 0 < ((x : ℤ) ^ 8 + (x : ℤ) ^ 4 + 1) * ((x : ℤ) ^ 2 * ((x : ℤ) ^ 2 - 1) ^ 2) := by
    have : (1 : ℤ) < (x : ℤ) ^ 2 := by nlinarith
    positivity
  linarith

theorem key2F4 {x : ℕ} (hx : 2 ≤ x) :
    (x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1) < (x ^ 12 - 1) * (x ^ 4 - 1) := by
  have h1 : 1 ≤ x := by omega
  have h2 : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ x ^ 12 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h4]
  have hX : (2 : ℤ) ≤ x := by exact_mod_cast hx
  have key : ((x : ℤ) ^ 12 - 1) * ((x : ℤ) ^ 4 - 1) -
      ((x : ℤ) ^ 6 + 1) * ((x : ℤ) ^ 4 - 1) * ((x : ℤ) ^ 3 + 1) * ((x : ℤ) - 1) =
      ((x : ℤ) ^ 4 - 1) * ((x : ℤ) ^ 6 + 1) * ((x : ℤ) ^ 3 + 1) * ((x : ℤ) ^ 3 - x) := by ring
  have hpos : 0 < ((x : ℤ) ^ 4 - 1) * ((x : ℤ) ^ 6 + 1) * ((x : ℤ) ^ 3 + 1) *
      ((x : ℤ) ^ 3 - x) := by
    have hx2 : (4 : ℤ) ≤ (x : ℤ) ^ 2 := by nlinarith
    have hx4 : (16 : ℤ) ≤ (x : ℤ) ^ 4 := by nlinarith
    have a1 : (0 : ℤ) < (x : ℤ) ^ 4 - 1 := by linarith
    have a2 : (0 : ℤ) < (x : ℤ) ^ 3 - x := by
      have e : (x : ℤ) ^ 3 - x = x * ((x : ℤ) ^ 2 - 1) := by ring
      rw [e]
      exact mul_pos (by linarith) (by linarith)
    positivity
  linarith

theorem false_of_b56_big {f u : ℕ} (hf : 1 ≤ f) (hu : Odd u) (hB : B56Card (2 ^ (12 * f) * u))
    (hlt : u < ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 4 - 1)) : False := by
  obtain ⟨x, hx⟩ : ∃ x, x = 2 ^ f := ⟨_, rfl⟩
  rw [← hx] at hlt
  have hx2 : 2 ≤ x := by
    rw [hx]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hpow : ∀ k : ℕ, (2 : ℕ) ^ (k * f) = x ^ k := fun k => by rw [hx, ← pow_mul, mul_comm]
  have m46 : x ^ 4 - 1 ≤ x ^ 6 - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (by norm_num)) 1
  have m48 : x ^ 4 - 1 ≤ x ^ 8 - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (by norm_num)) 1
  rcases hB.cases rfl hu with ⟨-, h⟩ | ⟨n, -, hn, h⟩ | ⟨n, -, hn, h⟩ | ⟨n, -, hn, h⟩ | h
  ·
    have h' : u = (x ^ 12) ^ 2 - 1 := by rw [h, hpow 12]
    have h1 : 1 ≤ x ^ 12 := Nat.one_le_pow _ _ (by omega)
    have h2 : x ^ 4 ≤ x ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : (x ^ 12 - 1) * (x ^ 4 - 1) ≤ (x ^ 12) ^ 2 - 1 := by
      have e : (x ^ 12) ^ 2 - 1 = (x ^ 12 - 1) * (x ^ 12 + 1) := by
        zify [h1, Nat.one_le_pow 2 (x ^ 12) (by positivity)]
        ring
      rw [e]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  ·
    obtain rfl : n = 4 * f := by omega
    have h' : u = (x ^ 8 - 1) * (x ^ 12 - 1) := by
      rw [h, hpow 4, ← pow_mul, ← pow_mul]
    have : (x ^ 12 - 1) * (x ^ 4 - 1) ≤ (x ^ 8 - 1) * (x ^ 12 - 1) := by
      rw [mul_comm]
      exact Nat.mul_le_mul m48 le_rfl
    omega
  ·
    obtain rfl : n = 3 * f := by omega
    have h' : u = (x ^ 6 - 1) * (x ^ 12 - 1) := by
      rw [h, hpow 3, ← pow_mul, ← pow_mul]
    have : (x ^ 12 - 1) * (x ^ 4 - 1) ≤ (x ^ 6 - 1) * (x ^ 12 - 1) := by
      rw [mul_comm]
      exact Nat.mul_le_mul m46 le_rfl
    omega
  ·
    obtain rfl : n = 2 * f := by omega
    have h' : u = (x ^ 12 - 1) * (x ^ 4 - 1) := by
      rw [h, hpow 2, ← pow_mul, ← pow_mul]
    omega
  ·
    have h12 : (2 : ℕ) ^ 12 ∣ 2 ^ (12 * f) * u :=
      dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by omega)) _
    rcases h with h | h | h | h | h | h <;> rw [h] at h12 <;> norm_num at h12

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
