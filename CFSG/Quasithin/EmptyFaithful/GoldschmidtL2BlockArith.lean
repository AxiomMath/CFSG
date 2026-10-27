module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.GoldL2

open Matrix

theorem sl2_sq_eq_one_of_pow_four {K : Type} [Field K] [CharP K 2]
    (g : SpecialLinearGroup (Fin 2) K) (h : g ^ 4 = 1) : g ^ 2 = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
  set M : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hM
  have h4 : M ^ 4 = 1 := by
    have := congrArg (fun x : SpecialLinearGroup (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) h
    simpa [hM] using this
  rw [det_fin_two] at hdet
  have e : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  have h4' : M * M * (M * M) = 1 := by
    have : M ^ 4 = M * M * (M * M) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [← this]; exact h4
  rw [e] at h4'
  simp only [Matrix.mul_fin_two] at h4'
  have e00 := congrFun (congrFun h4' 0) 0
  have e01 := congrFun (congrFun h4' 0) 1
  have e10 := congrFun (congrFun h4' 1) 0
  have e11 := congrFun (congrFun h4' 1) 1
  simp at e00 e01 e10 e11
  have hbc : b * c = a * d + 1 := by linear_combination (-1 : K) * hdet + (-1 : K) * h2
  have hb : b * (a + d) ^ 3 = 0 := by
    linear_combination e01 - (2 * b * (a + d)) * hbc - (b * (a + d)) * h2
  have ha : a * (a + d) ^ 3 + (a + d) ^ 2 = 0 := by
    linear_combination e00 - (2 + (b * c - a * d - 1) + (a + d) ^ 2 + 2 * a * (a + d)) * hbc
      - (a * (a + d)) * h2
  have hd : d * (a + d) ^ 3 + (a + d) ^ 2 = 0 := by
    linear_combination e11 - (2 + (b * c - a * d - 1) + (a + d) ^ 2 + 2 * d * (a + d)) * hbc
      - (d * (a + d)) * h2
  have ht : a + d = 0 := by
    by_contra ht
    have h1 : (a + d) ^ 2 * (a * (a + d) + 1) = 0 := by linear_combination ha
    have h1' : a * (a + d) + 1 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) ht
      · exact h
    have h2' : (a + d) ^ 2 * (d * (a + d) + 1) = 0 := by linear_combination hd
    have h2'' : d * (a + d) + 1 = 0 := by
      rcases mul_eq_zero.mp h2' with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) ht
      · exact h
    have : (a - d) * (a + d) = 0 := by linear_combination h1' - h2''
    rcases mul_eq_zero.mp this with h | h
    · apply ht
      have : a = d := sub_eq_zero.mp h
      rw [this]
      linear_combination d * h2
    · exact ht h
  apply Subtype.ext
  have hg2 : ((g ^ 2 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = M * M := by
    rw [sq, SpecialLinearGroup.coe_mul]
  rw [hg2, e, SpecialLinearGroup.coe_one]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination a * ht + hbc
  · linear_combination b * ht
  · linear_combination c * ht
  · linear_combination d * ht + hbc

def unitri3 (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by simp [det_fin_three]⟩

theorem unitri3_sq (K : Type) [Field K] [CharP K 2] :
    ((unitri3 K ^ 2 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [sq, SpecialLinearGroup.coe_mul]
  show !![(1 : K), 1, 0; 0, 1, 1; 0, 0, 1] * !![(1 : K), 1, 0; 0, 1, 1; 0, 0, 1] = _
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2

theorem unitri3_pow_four (K : Type) [Field K] [CharP K 2] : unitri3 K ^ 4 = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h4 : unitri3 K ^ 4 = (unitri3 K ^ 2) * (unitri3 K ^ 2) := by rw [← pow_add]
  apply Subtype.ext
  rw [h4, SpecialLinearGroup.coe_mul, unitri3_sq, SpecialLinearGroup.coe_one]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  linear_combination h2

theorem unitri3_sq_ne_one (K : Type) [Field K] [CharP K 2] : unitri3 K ^ 2 ≠ 1 := by
  intro h
  have := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) 0 2) h
  simp only [unitri3_sq, SpecialLinearGroup.coe_one] at this
  simp at this

theorem two_pow_mul_odd_eq {a c m m' : ℕ} (hm : Odd m) (hm' : Odd m')
    (h : 2 ^ a * m = 2 ^ c * m') : a = c ∧ m = m' := by
  wlog hac : a ≤ c generalizing a c m m'
  · obtain ⟨h1, h2⟩ := this hm' hm h.symm (by omega)
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hac
  have h' : m = 2 ^ d * m' := by
    have : 2 ^ a * m = 2 ^ a * (2 ^ d * m') := by rw [h, pow_add]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hd : d = 0 := by
    by_contra hd
    have : Even m := by
      rw [h']
      exact (Nat.even_pow.mpr ⟨even_two, hd⟩).mul_right m'
    exact (Nat.not_even_iff_odd.mpr hm) this
  subst hd
  simp only [pow_zero, one_mul] at h'
  exact ⟨by omega, h'⟩

theorem odd_four_pow_sub_one {a : ℕ} (ha : 1 ≤ a) : Odd (4 ^ a - 1) := by
  have h1 : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 2 ∣ 4 ^ a := dvd_pow (by norm_num) (by omega)
  rcases h2 with ⟨k, hk⟩
  exact ⟨k - 1, by omega⟩

theorem sl2_card_ne_sp4 {a b : ℕ} (ha : 3 ≤ a) (hb : 2 ≤ b)
    (h : 2 ^ a * (4 ^ a - 1) = (2 ^ b) ^ 4 * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 4 - 1))) : False := by
  have hq : 4 ≤ 2 ^ b := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hodd2 : Odd ((2 ^ b) ^ 2 - 1) := by
    have : (2 ^ b) ^ 2 = 4 ^ b := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]; exact odd_four_pow_sub_one (by omega)
  have hodd4 : Odd ((2 ^ b) ^ 4 - 1) := by
    have : (2 ^ b) ^ 4 = 4 ^ (2 * b) := by
      rw [← pow_mul, show 4 = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    rw [this]; exact odd_four_pow_sub_one (by omega)
  have e : (2 ^ b) ^ 4 = 2 ^ (4 * b) := by rw [← pow_mul, mul_comm]
  have h' : 2 ^ a * (4 ^ a - 1) = 2 ^ (4 * b) * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 4 - 1)) := by
    rw [h, e]
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_eq (odd_four_pow_sub_one (by omega)) (hodd2.mul hodd4) h'
  subst h1
  have e4 : 4 ^ (4 * b) = ((2 ^ b) ^ 4) ^ 2 := by
    rw [← pow_mul, show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  rw [e4] at h2
  set q := 2 ^ b with hqdef
  have hq1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq3 : 1 ≤ (q ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hq1, hq2, hq3] at h2
  have hqz : (4 : ℤ) ≤ q := by exact_mod_cast hq
  have h6 : (0 : ℤ) < (q : ℤ) ^ 6 := by positivity
  have h4 : (0 : ℤ) < (q : ℤ) ^ 4 := by positivity
  have h2' : (16 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
  ring_nf at h2
  nlinarith

theorem sl2_card_ne_fixed {n c : ℕ} (hn : 3 ≤ n)
    (hc : c = 60 ∨ c = 360 ∨ c = 2520 ∨ c = 20160 ∨ c = 9999360) : 2 ^ n * (4 ^ n - 1) ≠ c := by
  intro h
  by_cases h12 : 12 ≤ n
  · have h1 : 2 ^ 12 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h12
    have h2 : 4 ^ 12 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h12
    have h3 : 2 ^ 12 * (4 ^ 12 - 1) ≤ 2 ^ n * (4 ^ n - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
    norm_num at h3
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega
  · push Not at h12
    interval_cases n <;> rcases hc with rfl | rfl | rfl | rfl | rfl <;> norm_num at h

end CFSG.Quasithin.GoldL2
