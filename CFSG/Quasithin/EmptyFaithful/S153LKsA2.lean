module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin

namespace S153L

@[expose] def KsOrd (N : ℕ) : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧
    (N = 2 ^ n * (2 ^ (2 * n) - 1) ∨
      N = 2 ^ (2 * n) * (2 ^ (2 * n) + 1) * (2 ^ n - 1) ∨
      N = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) / 3 ∨
      N = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1) ∨
      N = 2 ^ (4 * n) * (2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1))

private theorem ksOrd_two_pow_mul_odd_inj {a b x y : ℕ} (hx : Odd x) (hy : Odd y)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  rcases le_total a b with hab | hab
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases k with _ | k
    · simpa using h'
    · exfalso
      rw [h', pow_succ, mul_comm (2 ^ k) 2, mul_assoc] at hx
      exact Nat.not_even_iff_odd.mpr hx (even_two_mul _)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h' := (Nat.eq_of_mul_eq_mul_left (by positivity) h).symm
    rcases k with _ | k
    · simpa using h'.symm
    · exfalso
      rw [h', pow_succ, mul_comm (2 ^ k) 2, mul_assoc] at hy
      exact Nat.not_even_iff_odd.mpr hy (even_two_mul _)

theorem ks_odd_two_pow_sub_one {k : ℕ} (hk : 0 < k) : Odd (2 ^ k - 1) := by
  have h : Even (2 ^ k) := (Nat.even_pow' hk.ne').mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h odd_one

private theorem ksOrd_odd_two_pow_add_one {k : ℕ} (hk : 0 < k) : Odd (2 ^ k + 1) :=
  ((Nat.even_pow' hk.ne').mpr even_two).add_one

theorem ks_three_dvd_two_pow_add_one {k : ℕ} (hk : Odd k) : 3 ∣ 2 ^ k + 1 := by
  simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hk

private theorem ksOrd_two_adic {N c t B : ℕ} (hc : c = 1 ∨ c = 3) (hB : Odd B)
    (hN : c * N = 2 ^ t * B) (h : KsOrd N) :
    ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧
      ((t = n ∧ c * (2 ^ (2 * n) - 1) = B) ∨
       (t = 2 * n ∧ c * ((2 ^ (2 * n) + 1) * (2 ^ n - 1)) = B) ∨
       (t = 3 * n ∧ c * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) = 3 * B) ∨
       (t = 3 * n ∧ c * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) = B) ∨
       (t = 4 * n ∧ c * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) = B)) := by
  have hco : Odd c := by rcases hc with rfl | rfl <;> decide
  obtain ⟨n, hn3, hodd, h1 | h2 | h3 | h4 | h5⟩ := h
  · subst h1
    have e : 2 ^ n * (c * (2 ^ (2 * n) - 1)) = 2 ^ t * B := by rw [← hN]; ring
    obtain ⟨e1, e2⟩ := ksOrd_two_pow_mul_odd_inj
      (hco.mul (ks_odd_two_pow_sub_one (by omega))) hB e
    exact ⟨n, hn3, hodd, Or.inl ⟨e1.symm, e2⟩⟩
  · subst h2
    have e : 2 ^ (2 * n) * (c * ((2 ^ (2 * n) + 1) * (2 ^ n - 1))) = 2 ^ t * B := by
      rw [← hN]; ring
    obtain ⟨e1, e2⟩ := ksOrd_two_pow_mul_odd_inj
      (hco.mul ((ksOrd_odd_two_pow_add_one (by omega)).mul (ks_odd_two_pow_sub_one (by omega)))) hB e
    exact ⟨n, hn3, hodd, Or.inr (Or.inl ⟨e1.symm, e2⟩)⟩
  · have hd : 3 ∣ 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) :=
      Dvd.dvd.mul_left (ks_three_dvd_two_pow_add_one ((by decide : Odd 3).mul hodd)) _
    have hP := Nat.mul_div_cancel' hd
    have e : 2 ^ (3 * n) * (c * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))) = 2 ^ t * (3 * B) := by
      calc _ = c * (2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by ring
        _ = c * (3 * N) := by rw [h3, hP]
        _ = 3 * (c * N) := by ring
        _ = 2 ^ t * (3 * B) := by rw [hN]; ring
    obtain ⟨e1, e2⟩ := ksOrd_two_pow_mul_odd_inj
      (hco.mul ((ks_odd_two_pow_sub_one (by omega)).mul (ksOrd_odd_two_pow_add_one (by omega))))
      ((by decide : Odd 3).mul hB) e
    exact ⟨n, hn3, hodd, Or.inr (Or.inr (Or.inl ⟨e1.symm, e2⟩))⟩
  · subst h4
    have e : 2 ^ (3 * n) * (c * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1))) = 2 ^ t * B := by
      rw [← hN]; ring
    obtain ⟨e1, e2⟩ := ksOrd_two_pow_mul_odd_inj
      (hco.mul ((ks_odd_two_pow_sub_one (by omega)).mul (ks_odd_two_pow_sub_one (by omega)))) hB e
    exact ⟨n, hn3, hodd, Or.inr (Or.inr (Or.inr (Or.inl ⟨e1.symm, e2⟩)))⟩
  · subst h5
    have e : 2 ^ (4 * n) * (c * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1))) = 2 ^ t * B := by
      rw [← hN]; ring
    obtain ⟨e1, e2⟩ := ksOrd_two_pow_mul_odd_inj
      (hco.mul ((ks_odd_two_pow_sub_one (by omega)).mul (ks_odd_two_pow_sub_one (by omega)))) hB e
    exact ⟨n, hn3, hodd, Or.inr (Or.inr (Or.inr (Or.inr ⟨e1.symm, e2⟩)))⟩

private theorem ksOrd_cases {N : ℕ} (h : KsOrd N) :
    N = 504 ∨ N = 29120 ∨ N = 5515776 ∨ N = 32736 ∨ N = 2097024 ∨ 10000000 < N := by
  obtain ⟨n, hn3, ⟨k, hk⟩, h1 | h2 | h3 | h4 | h5⟩ := h
  · rcases Nat.lt_or_ge n 9 with h9 | h9
    · have : n = 3 ∨ n = 5 ∨ n = 7 := by omega
      rcases this with rfl | rfl | rfl
      · left; rw [h1]; norm_num
      · right; right; right; left; rw [h1]; norm_num
      · right; right; right; right; left; rw [h1]; norm_num
    · right; right; right; right; right
      have h1' : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h9
      have h2' : 2 ^ 18 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ 9 * (2 ^ 18 - 1) ≤ 2 ^ n * (2 ^ (2 * n) - 1) :=
        Nat.mul_le_mul h1' (Nat.sub_le_sub_right h2' 1)
      omega
  · rcases Nat.lt_or_ge n 5 with h5 | h5
    · have : n = 3 := by omega
      subst this
      right; left; rw [h2]; norm_num
    · right; right; right; right; right
      have h1' : 2 ^ 10 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2' : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
      have : 2 ^ 10 * (2 ^ 10 + 1) * (2 ^ 5 - 1) ≤
          2 ^ (2 * n) * (2 ^ (2 * n) + 1) * (2 ^ n - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1' (by omega)) (Nat.sub_le_sub_right h2' 1)
      omega
  · rcases Nat.lt_or_ge n 5 with h5 | h5
    · have : n = 3 := by omega
      subst this
      right; right; left; rw [h3]; norm_num
    · right; right; right; right; right
      have h1' : 2 ^ 15 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2' : 2 ^ 10 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ 15 * (2 ^ 10 - 1) * (2 ^ 15 + 1) / 3 ≤
          2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) / 3 :=
        Nat.div_le_div_right (Nat.mul_le_mul (Nat.mul_le_mul h1' (Nat.sub_le_sub_right h2' 1))
          (by omega))
      omega
  · right; right; right; right; right
    have h1' : 2 ^ 9 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2' : 2 ^ 6 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 9 * (2 ^ 6 - 1) * (2 ^ 9 - 1) ≤
        2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1' (Nat.sub_le_sub_right h2' 1)) (Nat.sub_le_sub_right h1' 1)
    omega
  · right; right; right; right; right
    have h1' : 2 ^ 12 ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2' : 2 ^ 6 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 12 * (2 ^ 6 - 1) * (2 ^ 12 - 1) ≤
        2 ^ (4 * n) * (2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1' (Nat.sub_le_sub_right h2' 1)) (Nat.sub_le_sub_right h1' 1)
    omega

theorem ksOrd_ge {N : ℕ} (h : KsOrd N) : 504 ≤ N := by
  rcases ksOrd_cases h with h | h | h | h | h | h <;> omega

theorem ksOrd_ne_fixed {N : ℕ} (h : KsOrd N) :
    N ≠ 360 ∧ N ≠ 720 ∧ N ≠ 1080 ∧ N ≠ 2520 ∧ N ≠ 6048 ∧ N ≠ 12096 ∧ N ≠ 20160 ∧ N ≠ 443520 ∧
      N ≠ 1330560 ∧ N ≠ 9999360 := by
  rcases ksOrd_cases h with h | h | h | h | h | h <;> omega

theorem ksOrd_ne_g2 {m : ℕ} (hm : 2 ≤ m) :
    ¬ KsOrd (2 ^ (6 * m) * ((2 ^ (6 * m) - 1) * (2 ^ (2 * m) - 1))) := by
  intro hK
  have hB : Odd ((2 ^ (6 * m) - 1) * (2 ^ (2 * m) - 1)) :=
    (ks_odd_two_pow_sub_one (by omega)).mul (ks_odd_two_pow_sub_one (by omega))
  obtain ⟨n, hn3, hodd, h⟩ :=
    ksOrd_two_adic (c := 1) (t := 6 * m) (Or.inl rfl) hB (by rw [one_mul]) hK
  obtain ⟨k, hk⟩ := hodd
  have h26 : 2 ^ (2 * m) < 2 ^ (3 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1a : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  have h1b : 1 ≤ 2 ^ (6 * m) := Nat.one_le_two_pow
  have h6 : 2 ^ (3 * m) < 2 ^ (6 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases h with ⟨h1, -⟩ | ⟨h2, h2'⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, h5'⟩
  · omega
  · have hn : n = 3 * m := by omega
    subst hn
    rw [one_mul, show 2 * (3 * m) = 6 * m by ring] at h2'
    have hlt : (2 ^ (6 * m) - 1) * (2 ^ (2 * m) - 1) < (2 ^ (6 * m) + 1) * (2 ^ (3 * m) - 1) :=
      Nat.mul_lt_mul'' (by omega) (by omega)
    omega
  · omega
  · omega
  · have hn : 3 * m = 2 * n := by omega
    rw [one_mul, show 4 * n = 6 * m by omega, show 2 * n = 3 * m by omega] at h5'
    have hlt : (2 ^ (6 * m) - 1) * (2 ^ (2 * m) - 1) < (2 ^ (6 * m) - 1) * (2 ^ (3 * m) - 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    rw [mul_comm (2 ^ (3 * m) - 1)] at h5'
    omega

theorem ksOrd_ne_orth {a : ℕ} (ha : 1 ≤ a) : ¬ KsOrd (2 ^ (2 * a) * (2 ^ (4 * a) - 1)) := by
  intro hK
  obtain ⟨n, hn3, hodd, h⟩ := ksOrd_two_adic (c := 1) (t := 2 * a) (Or.inl rfl)
    (ks_odd_two_pow_sub_one (k := 4 * a) (by omega)) (by rw [one_mul]) hK
  obtain ⟨k, hk⟩ := hodd
  rcases h with ⟨h1, -⟩ | ⟨h2, h2'⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, h5'⟩
  · omega
  · have hn : n = a := by omega
    subst hn
    rw [one_mul] at h2'
    have hsq : 2 ^ (4 * n) - 1 = (2 ^ (2 * n) + 1) * (2 ^ (2 * n) - 1) := by
      have e : 2 ^ (4 * n) = 2 ^ (2 * n) * 2 ^ (2 * n) := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      have := Nat.mul_self_sub_mul_self_eq (2 ^ (2 * n)) 1
      simpa using this
    have hlt : (2 ^ (2 * n) + 1) * (2 ^ n - 1) < (2 ^ (2 * n) + 1) * (2 ^ (2 * n) - 1) := by
      apply Nat.mul_lt_mul_of_pos_left _ (Nat.succ_pos _)
      have : 2 ^ n < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    omega
  · omega
  · omega
  · have hn : a = 2 * n := by omega
    subst hn
    rw [one_mul, show 4 * (2 * n) = 4 * n + 4 * n by ring, pow_add] at h5'
    have hy : 2 ≤ 2 ^ (4 * n) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsq : 2 ^ (4 * n) * 2 ^ (4 * n) - 1 = (2 ^ (4 * n) + 1) * (2 ^ (4 * n) - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (2 ^ (4 * n)) 1
      simpa using this
    have h24 : 2 ^ (2 * n) < 2 ^ (4 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hlt : (2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1) < (2 ^ (4 * n) + 1) * (2 ^ (4 * n) - 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega

theorem ksOrd_not_prime {N : ℕ} (h : KsOrd N) : ¬ N.Prime := by
  obtain ⟨n, hn3, hodd, h1 | h2 | h3 | h4 | h5⟩ := h
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h64 : 64 ≤ 2 ^ (2 * n) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    subst h1
    exact Nat.not_prime_mul (by omega) (by omega)
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h64 : 64 ≤ 2 ^ (2 * n) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    subst h2
    refine Nat.not_prime_mul (fun h => ?_) (by omega)
    have := Nat.eq_one_of_mul_eq_one_right h
    omega
  · have h512 : 512 ≤ 2 ^ (3 * n) := by
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h64 : 64 ≤ 2 ^ (2 * n) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h3, Nat.mul_div_assoc _ (ks_three_dvd_two_pow_add_one ((by decide : Odd 3).mul hodd))]
    refine Nat.not_prime_mul (fun h => ?_) (by omega)
    have := Nat.eq_one_of_mul_eq_one_right h
    omega
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h512 : 512 ≤ 2 ^ (3 * n) := by
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h64 : 64 ≤ 2 ^ (2 * n) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    subst h4
    refine Nat.not_prime_mul (fun h => ?_) (by omega)
    have := Nat.eq_one_of_mul_eq_one_right h
    omega
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h4096 : 4096 ≤ 2 ^ (4 * n) := by
      calc 4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h64 : 64 ≤ 2 ^ (2 * n) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    subst h5
    refine Nat.not_prime_mul (fun h => ?_) (by omega)
    have := Nat.eq_one_of_mul_eq_one_right h
    omega

end S153L

end CFSG.Quasithin
