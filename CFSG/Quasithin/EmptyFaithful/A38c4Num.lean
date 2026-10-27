module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.A318Excl

private theorem pow_two_eq_of_mul_odd {a b x y : ℕ} (hx : Odd x) (hy : Odd y)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h2 : x = 2 ^ (c + 1) * y := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ a by positivity)
      rw [h]; ring
    have h3 : x = 2 * (2 ^ c * y) := by rw [h2]; ring
    have := Nat.odd_iff.mp hx
    omega
  · exact hab
  · exfalso
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h2 : y = 2 ^ (c + 1) * x := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ b by positivity)
      rw [← h]; ring
    have h3 : y = 2 * (2 ^ c * x) := by rw [h2]; ring
    have := Nat.odd_iff.mp hy
    omega

private theorem two_adic_aux {t j A W : ℕ} (hA : Odd A) (ht : 1 ≤ t)
    (hW : W = t ^ 2 * (t + 1) ∨ W = t * (t + 1) ^ 2) (h : 2 ^ (j + 3) ∣ A * (8 * W)) :
    2 ^ (j + 2) ≤ (2 * t + 2) ^ 2 := by
  have hcop : Nat.Coprime (2 ^ (j + 3)) A :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hA)
  have h1 : 2 ^ (j + 3) ∣ 8 * W := hcop.dvd_of_dvd_mul_left h
  have h2 : 2 ^ j ∣ W := by
    have : 8 * 2 ^ j ∣ 8 * W := by
      have e : 2 ^ (j + 3) = 8 * 2 ^ j := by rw [pow_add]; ring
      rwa [e] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hjpos : 0 < 2 ^ j := by positivity
  have e4 : 2 ^ (j + 2) = 4 * 2 ^ j := by rw [pow_add]; ring
  rcases Nat.even_or_odd t with he | ho
  ·
    have hodd : Odd (t + 1) := he.add_one
    have hc1 : Nat.Coprime (2 ^ j) (t + 1) := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have hc2 : Nat.Coprime (2 ^ j) ((t + 1) ^ 2) := Nat.Coprime.pow_right _ hc1
    rcases hW with rfl | rfl
    · have h3 : 2 ^ j ∣ t ^ 2 := hc1.dvd_of_dvd_mul_right h2
      have h4 : 2 ^ j ≤ t ^ 2 := Nat.le_of_dvd (by positivity) h3
      rw [e4]
      nlinarith
    · have h3 : 2 ^ j ∣ t := hc2.dvd_of_dvd_mul_right h2
      have h4 : 2 ^ j ≤ t := Nat.le_of_dvd (by omega) h3
      rw [e4]
      nlinarith
  ·
    have hc1 : Nat.Coprime (2 ^ j) t := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ho)
    have hc2 : Nat.Coprime (2 ^ j) (t ^ 2) := Nat.Coprime.pow_right _ hc1
    rcases hW with rfl | rfl
    · have h3 : 2 ^ j ∣ t + 1 := hc2.dvd_of_dvd_mul_left h2
      have h4 : 2 ^ j ≤ t + 1 := Nat.le_of_dvd (by omega) h3
      rw [e4]
      nlinarith
    · have h3 : 2 ^ j ∣ (t + 1) ^ 2 := hc1.dvd_of_dvd_mul_left h2
      have h4 : 2 ^ j ≤ (t + 1) ^ 2 := Nat.le_of_dvd (by positivity) h3
      rw [e4]
      nlinarith

private theorem odd_L3_bound {t j d T : ℕ} (ht : 1 ≤ t) (hT : 2 ^ (j + 3) ∣ T)
    (h : (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 - 1)) = d * T) :
    2 ^ (j + 2) ≤ (2 * t + 2) ^ 2 := by
  have e1 : (2 * t + 1) ^ 2 - 1 = 4 * t * (t + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e2 : (2 * t + 1) ^ 3 - 1 = 2 * t * ((2 * t + 1) ^ 2 + (2 * t + 1) + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  have hA : Odd ((2 * t + 1) ^ 3 * ((2 * t + 1) ^ 2 + (2 * t + 1) + 1)) := by
    refine Odd.mul (Odd.pow ⟨t, rfl⟩) ⟨2 * t ^ 2 + 3 * t + 1, by ring⟩
  have hN : 2 ^ (j + 3) ∣ ((2 * t + 1) ^ 3 * ((2 * t + 1) ^ 2 + (2 * t + 1) + 1)) *
      (8 * (t ^ 2 * (t + 1))) := by
    have : ((2 * t + 1) ^ 3 * ((2 * t + 1) ^ 2 + (2 * t + 1) + 1)) * (8 * (t ^ 2 * (t + 1))) =
        d * T := by
      rw [← h, e1, e2]; ring
    rw [this]
    exact Dvd.dvd.mul_left hT d
  exact two_adic_aux hA ht (Or.inl rfl) hN

private theorem odd_U3_bound {t j d T : ℕ} (ht : 1 ≤ t) (hT : 2 ^ (j + 3) ∣ T)
    (h : (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 + 1)) = d * T) :
    2 ^ (j + 2) ≤ (2 * t + 2) ^ 2 := by
  have e1 : (2 * t + 1) ^ 2 - 1 = 4 * t * (t + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  have hA : Odd ((2 * t + 1) ^ 3 * (4 * t ^ 2 + 2 * t + 1)) := by
    refine Odd.mul (Odd.pow ⟨t, rfl⟩) ⟨2 * t ^ 2 + t, by ring⟩
  have hN : 2 ^ (j + 3) ∣ ((2 * t + 1) ^ 3 * (4 * t ^ 2 + 2 * t + 1)) *
      (8 * (t * (t + 1) ^ 2)) := by
    have : ((2 * t + 1) ^ 3 * (4 * t ^ 2 + 2 * t + 1)) * (8 * (t * (t + 1) ^ 2)) =
        d * T := by
      rw [← h, e1]; ring
    rw [this]
    exact Dvd.dvd.mul_left hT d
  exact two_adic_aux hA ht (Or.inr rfl) hN

private theorem pow_eight_le_four_mul {Q : ℕ} (hQ : 2 ≤ Q) :
    Q ^ 8 ≤ 4 * (Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) := by
  have h1 : Q ^ 2 ≤ 2 * (Q ^ 2 - 1) := by
    have : 4 ≤ Q ^ 2 := by nlinarith
    omega
  have h2 : Q ^ 3 ≤ 2 * (Q ^ 3 - 1) := by
    have : 8 ≤ Q ^ 3 := by nlinarith [Nat.pow_le_pow_left hQ 3]
    omega
  have h3 : Q ^ 2 * Q ^ 3 ≤ (2 * (Q ^ 2 - 1)) * (2 * (Q ^ 3 - 1)) := Nat.mul_le_mul h1 h2
  calc Q ^ 8 = Q ^ 3 * (Q ^ 2 * Q ^ 3) := by ring
    _ ≤ Q ^ 3 * ((2 * (Q ^ 2 - 1)) * (2 * (Q ^ 3 - 1))) := Nat.mul_le_mul_left _ h3
    _ = 4 * (Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) := by ring

private theorem N_L_le_N_U (Q : ℕ) :
    Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

private theorem big_S {y Q : ℕ} (hy : 16 ≤ y) (hQ : 3 ≤ Q) (h : y ^ 2 ≤ 2 * (Q + 1) ^ 2) :
    3 * (y ^ 2 * ((y - 1) * (y ^ 2 - 1))) < Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
  have hQy : y ≤ 2 * Q := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h8 := pow_eight_le_four_mul (Q := Q) (by omega)
  have h9 : y ^ 8 ≤ 256 * Q ^ 8 := by
    calc y ^ 8 ≤ (2 * Q) ^ 8 := Nat.pow_le_pow_left hQy 8
      _ = 256 * Q ^ 8 := by ring
  have hT : y ^ 2 * ((y - 1) * (y ^ 2 - 1)) ≤ y ^ 5 := by
    calc y ^ 2 * ((y - 1) * (y ^ 2 - 1)) ≤ y ^ 2 * (y * y ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      _ = y ^ 5 := by ring
  have hy3 : 4096 ≤ y ^ 3 := by
    calc 4096 = 16 ^ 3 := by norm_num
      _ ≤ y ^ 3 := Nat.pow_le_pow_left hy 3
  have hy5 : 0 < y ^ 5 := by positivity
  have h10 : 4096 * y ^ 5 ≤ y ^ 8 := by
    calc 4096 * y ^ 5 ≤ y ^ 3 * y ^ 5 := Nat.mul_le_mul_right _ hy3
      _ = y ^ 8 := by ring
  nlinarith

private theorem big_G {y Q : ℕ} (hy : 16 ≤ y) (hQ : 3 ≤ Q) (h : y ^ 3 ≤ 2 * (Q + 1) ^ 2) :
    3 * (y ^ 3 * ((y ^ 3 - 1) * (y - 1))) < Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
  have hQy : y ≤ Q := by
    by_contra hcon
    push Not at hcon
    have h1 : Q + 1 ≤ y := hcon
    have h2 : 2 * (Q + 1) ^ 2 ≤ 2 * y ^ 2 := by
      have := Nat.pow_le_pow_left h1 2
      omega
    have h3 : 2 * y ^ 2 < y ^ 3 := by nlinarith
    omega
  have h8 := pow_eight_le_four_mul (Q := Q) (by omega)
  have h9 : y ^ 8 ≤ Q ^ 8 := Nat.pow_le_pow_left hQy 8
  have hT : y ^ 3 * ((y ^ 3 - 1) * (y - 1)) ≤ y ^ 7 := by
    calc y ^ 3 * ((y ^ 3 - 1) * (y - 1)) ≤ y ^ 3 * (y ^ 3 * y) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      _ = y ^ 7 := by ring
  have hy7 : 0 < y ^ 7 := by positivity
  have h10 : 16 * y ^ 7 ≤ y ^ 8 := by
    calc 16 * y ^ 7 ≤ y * y ^ 7 := Nat.mul_le_mul_right _ hy
      _ = y ^ 8 := by ring
  nlinarith

private theorem sq_pow_two_pow_eq (n j : ℕ) (hj : 4 * n = j + 3) : (2 ^ (2 * n)) ^ 2 = 2 ^ (j + 3) := by
  rw [← pow_mul, ← hj]; congr 1; ring

private theorem sixteen_le_two_pow_two_mul {n : ℕ} (hn : 2 ≤ n) : 16 ≤ 2 ^ (2 * n) := by
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem two_pow_succ_le {j a : ℕ} (h : 2 ^ (j + 2) ≤ a ^ 2) : 2 ^ (j + 3) ≤ 2 * a ^ 2 := by
  have : 2 ^ (j + 3) = 2 * 2 ^ (j + 2) := by rw [pow_succ]; ring
  omega

private theorem no_psl3_sp4_odd {t n d : ℕ} (hn : 2 ≤ n) (ht : 1 ≤ t) (hd : d ≤ 3) :
    (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 - 1)) ≠
      d * ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1))) := by
  intro h
  obtain ⟨j, hj⟩ : ∃ j, 4 * n = j + 3 := ⟨4 * n - 3, by omega⟩
  have hy := sq_pow_two_pow_eq n j hj
  have hdvd : 2 ^ (j + 3) ∣
      (2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1)) := by
    rw [hy]; exact Dvd.intro _ rfl
  have h1 := odd_L3_bound ht hdvd h
  have h2 : (2 ^ (2 * n)) ^ 2 ≤ 2 * (2 * t + 1 + 1) ^ 2 := by
    rw [hy]; exact two_pow_succ_le h1
  have hb := big_S (sixteen_le_two_pow_two_mul hn) (by omega) h2
  have h3 : d * ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1))) ≤
      3 * ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1))) :=
    Nat.mul_le_mul_right _ hd
  omega

private theorem no_psu3_sp4_odd {t n d : ℕ} (hn : 2 ≤ n) (ht : 1 ≤ t) (hd : d ≤ 3) :
    (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 + 1)) ≠
      d * ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1))) := by
  intro h
  obtain ⟨j, hj⟩ : ∃ j, 4 * n = j + 3 := ⟨4 * n - 3, by omega⟩
  have hy := sq_pow_two_pow_eq n j hj
  have hdvd : 2 ^ (j + 3) ∣
      (2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1)) := by
    rw [hy]; exact Dvd.intro _ rfl
  have h1 := odd_U3_bound ht hdvd h
  have h2 : (2 ^ (2 * n)) ^ 2 ≤ 2 * (2 * t + 1 + 1) ^ 2 := by
    rw [hy]; exact two_pow_succ_le h1
  have hb := big_S (sixteen_le_two_pow_two_mul hn) (by omega) h2
  have h3 : d * ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1))) ≤
      3 * ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1))) :=
    Nat.mul_le_mul_right _ hd
  have h4 := N_L_le_N_U (2 * t + 1)
  omega

private theorem cube_pow_two_pow_eq (n j : ℕ) (hj : 6 * n = j + 3) : (2 ^ (2 * n)) ^ 3 = 2 ^ (j + 3) := by
  rw [← pow_mul, ← hj]; congr 1; ring

private theorem no_psl3_g2_odd {t n d : ℕ} (hn : 2 ≤ n) (ht : 1 ≤ t) (hd : d ≤ 3) :
    (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 - 1)) ≠
      d * ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1))) := by
  intro h
  obtain ⟨j, hj⟩ : ∃ j, 6 * n = j + 3 := ⟨6 * n - 3, by omega⟩
  have hy := cube_pow_two_pow_eq n j hj
  have hdvd : 2 ^ (j + 3) ∣
      (2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1)) := by
    rw [hy]; exact Dvd.intro _ rfl
  have h1 := odd_L3_bound ht hdvd h
  have h2 : (2 ^ (2 * n)) ^ 3 ≤ 2 * (2 * t + 1 + 1) ^ 2 := by
    rw [hy]; exact two_pow_succ_le h1
  have hb := big_G (sixteen_le_two_pow_two_mul hn) (by omega) h2
  have h3 : d * ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1))) ≤
      3 * ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1))) :=
    Nat.mul_le_mul_right _ hd
  omega

private theorem no_psu3_g2_odd {t n d : ℕ} (hn : 2 ≤ n) (ht : 1 ≤ t) (hd : d ≤ 3) :
    (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 + 1)) ≠
      d * ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1))) := by
  intro h
  obtain ⟨j, hj⟩ : ∃ j, 6 * n = j + 3 := ⟨6 * n - 3, by omega⟩
  have hy := cube_pow_two_pow_eq n j hj
  have hdvd : 2 ^ (j + 3) ∣
      (2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1)) := by
    rw [hy]; exact Dvd.intro _ rfl
  have h1 := odd_U3_bound ht hdvd h
  have h2 : (2 ^ (2 * n)) ^ 3 ≤ 2 * (2 * t + 1 + 1) ^ 2 := by
    rw [hy]; exact two_pow_succ_le h1
  have hb := big_G (sixteen_le_two_pow_two_mul hn) (by omega) h2
  have h3 : d * ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1))) ≤
      3 * ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1))) :=
    Nat.mul_le_mul_right _ hd
  have h4 := N_L_le_N_U (2 * t + 1)
  omega

private theorem odd_two_pow_sub_one' {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ]
  have : 1 ≤ 2 ^ m' := Nat.one_le_two_pow
  exact ⟨2 ^ m' - 1, by omega⟩

private theorem odd_two_pow_add_one' {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m + 1) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ]
  exact ⟨2 ^ m', by ring⟩

private theorem even_exp_generic {e a M m d : ℕ} (hM : Odd M) (hm : Odd m) (hd : Odd d)
    (h : (2 ^ e) ^ 3 * M = d * (2 ^ a * m)) : 3 * e = a := by
  have e1 : (2 ^ e) ^ 3 = 2 ^ (3 * e) := by rw [← pow_mul, mul_comm]
  rw [e1] at h
  exact pow_two_eq_of_mul_odd hM (hd.mul hm) (by rw [h]; ring)

private theorem odd_gcd_three (m : ℕ) : Odd (Nat.gcd 3 m) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 m) with h | h <;> rw [h]
  · exact odd_one
  · exact ⟨1, by norm_num⟩

private theorem gcd_three_sub_eq (m : ℕ) : Nat.gcd 3 (2 ^ (2 * m) - 1) = 3 := by
  apply Nat.gcd_eq_left
  have : (4 : ℕ) - 1 ∣ 4 ^ m - 1 ^ m := Nat.sub_dvd_pow_sub_pow 4 1 m
  rw [one_pow] at this
  rw [pow_mul]
  simpa using this

private theorem gcd_three_add_eq (m : ℕ) : Nat.gcd 3 (2 ^ (2 * m) + 1) = 1 := by
  have h1 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have h2 : ¬ 3 ∣ 2 ^ (2 * m) + 1 := by
    rw [pow_mul]
    norm_num
    omega
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h2

private theorem alg_L3_S {x : ℕ} (hx : 2 ≤ x) :
    (x ^ 4) ^ 3 * (((x ^ 4) ^ 2 - 1) * ((x ^ 4) ^ 3 - 1)) ≠
      3 * ((x ^ 6) ^ 2 * ((x ^ 6 - 1) * ((x ^ 6) ^ 2 - 1))) := by
  intro h
  have e1 : (x ^ 4) ^ 3 = x ^ 12 := by rw [← pow_mul]
  have e2 : (x ^ 4) ^ 2 = x ^ 8 := by rw [← pow_mul]
  have e3 : (x ^ 6) ^ 2 = x ^ 12 := by rw [← pow_mul]
  rw [e1, e2, e3] at h
  have hx12 : 4096 ≤ x ^ 12 := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ x ^ 12 := Nat.pow_le_pow_left hx 12
  have hpos : 0 < x ^ 12 * (x ^ 12 - 1) := Nat.mul_pos (by omega) (by omega)
  have h2 : (x ^ 12 * (x ^ 12 - 1)) * (x ^ 8 - 1) =
      (x ^ 12 * (x ^ 12 - 1)) * (3 * (x ^ 6 - 1)) := by
    calc (x ^ 12 * (x ^ 12 - 1)) * (x ^ 8 - 1) = x ^ 12 * ((x ^ 8 - 1) * (x ^ 12 - 1)) := by ring
      _ = 3 * (x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1))) := h
      _ = (x ^ 12 * (x ^ 12 - 1)) * (3 * (x ^ 6 - 1)) := by ring
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  have hx6 : 64 ≤ x ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ x ^ 6 := Nat.pow_le_pow_left hx 6
  have hx8 : 4 * x ^ 6 ≤ x ^ 8 := by
    have : 4 ≤ x ^ 2 := by nlinarith
    calc 4 * x ^ 6 ≤ x ^ 2 * x ^ 6 := Nat.mul_le_mul_right _ this
      _ = x ^ 8 := by ring
  generalize x ^ 6 = u at *
  generalize x ^ 8 = w at *
  omega

private theorem alg_U3_S {x : ℕ} (hx : 2 ≤ x) :
    (x ^ 4) ^ 3 * (((x ^ 4) ^ 2 - 1) * ((x ^ 4) ^ 3 + 1)) ≠
      1 * ((x ^ 6) ^ 2 * ((x ^ 6 - 1) * ((x ^ 6) ^ 2 - 1))) := by
  intro h
  have e1 : (x ^ 4) ^ 3 = x ^ 12 := by rw [← pow_mul]
  have e2 : (x ^ 4) ^ 2 = x ^ 8 := by rw [← pow_mul]
  have e3 : (x ^ 6) ^ 2 = x ^ 12 := by rw [← pow_mul]
  rw [e1, e2, e3] at h
  have hx12 : 4096 ≤ x ^ 12 := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ x ^ 12 := Nat.pow_le_pow_left hx 12
  have hpos : 0 < x ^ 12 := by omega
  have h2 : x ^ 12 * ((x ^ 8 - 1) * (x ^ 12 + 1)) = x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1)) := by
    rw [h]; ring
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  have hx6 : 64 ≤ x ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ x ^ 6 := Nat.pow_le_pow_left hx 6
  have hx8 : x ^ 6 ≤ x ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  generalize x ^ 6 = u at *
  generalize x ^ 8 = w at *
  generalize x ^ 12 = c at *
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h3
  nlinarith

private theorem alg_L3_G {y : ℕ} (hy : 16 ≤ y) :
    y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 - 1)) ≠ 3 * (y ^ 3 * ((y ^ 3 - 1) * (y - 1))) := by
  intro h
  have hy3 : 4096 ≤ y ^ 3 := by
    calc 4096 = 16 ^ 3 := by norm_num
      _ ≤ y ^ 3 := Nat.pow_le_pow_left hy 3
  have hpos : 0 < y ^ 3 * (y ^ 3 - 1) := Nat.mul_pos (by omega) (by omega)
  have h2 : (y ^ 3 * (y ^ 3 - 1)) * (y ^ 2 - 1) = (y ^ 3 * (y ^ 3 - 1)) * (3 * (y - 1)) := by
    calc (y ^ 3 * (y ^ 3 - 1)) * (y ^ 2 - 1) = y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 - 1)) := by ring
      _ = 3 * (y ^ 3 * ((y ^ 3 - 1) * (y - 1))) := h
      _ = (y ^ 3 * (y ^ 3 - 1)) * (3 * (y - 1)) := by ring
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  have hy2 : 16 * y ≤ y ^ 2 := by nlinarith
  generalize y ^ 2 = w at *
  omega

private theorem alg_U3_G {y : ℕ} (hy : 16 ≤ y) :
    y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 + 1)) ≠ 1 * (y ^ 3 * ((y ^ 3 - 1) * (y - 1))) := by
  intro h
  have hy3 : 4096 ≤ y ^ 3 := by
    calc 4096 = 16 ^ 3 := by norm_num
      _ ≤ y ^ 3 := Nat.pow_le_pow_left hy 3
  have hpos : 0 < y ^ 3 := by omega
  have h2 : y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 + 1)) = y ^ 3 * ((y ^ 3 - 1) * (y - 1)) := by
    rw [h]; ring
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  have hy2 : 16 * y ≤ y ^ 2 := by nlinarith
  generalize y ^ 2 = w at *
  generalize y ^ 3 = c at *
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h3
  nlinarith

private theorem even_L3_S {e n d : ℕ} (he : 1 ≤ e) (hn : 2 ≤ n) (hd : d = Nat.gcd 3 (2 ^ e - 1))
    (h : (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) =
      d * ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1)))) : False := by
  have hdodd : Odd d := hd ▸ odd_gcd_three _
  have hA : Odd ((2 ^ e) ^ 2 - 1) := by
    have := odd_two_pow_sub_one' (m := e * 2) (by omega)
    rwa [pow_mul] at this
  have hB : Odd ((2 ^ e) ^ 3 - 1) := by
    have := odd_two_pow_sub_one' (m := e * 3) (by omega)
    rwa [pow_mul] at this
  have hC : Odd (2 ^ (2 * n) - 1) := odd_two_pow_sub_one' (by omega)
  have hD : Odd ((2 ^ (2 * n)) ^ 2 - 1) := by
    have := odd_two_pow_sub_one' (m := 2 * n * 2) (by omega)
    rwa [pow_mul] at this
  have h3 : 3 * e = 4 * n := by
    refine even_exp_generic (M := ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1))
      (m := (2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1)) (d := d) (hA.mul hB) (hC.mul hD)
      hdodd ?_
    have e2 : (2 ^ (2 * n)) ^ 2 = 2 ^ (4 * n) := by rw [← pow_mul]; congr 1; ring
    rw [h]
    rw [e2]
  obtain ⟨j, hj1, hj2⟩ : ∃ j, e = 4 * j ∧ n = 3 * j := ⟨e / 4, by omega, by omega⟩
  subst hj1 hj2
  have hx : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQ : 2 ^ (4 * j) = (2 ^ j) ^ 4 := by rw [← pow_mul, mul_comm]
  have hy : 2 ^ (2 * (3 * j)) = (2 ^ j) ^ 6 := by rw [← pow_mul]; congr 1; ring
  have hdv : d = 3 := by rw [hd, show 4 * j = 2 * (2 * j) by ring, gcd_three_sub_eq]
  rw [hQ, hy, hdv] at h
  exact alg_L3_S hx h

private theorem even_U3_S {e n d : ℕ} (he : 1 ≤ e) (hn : 2 ≤ n) (hd : d = Nat.gcd 3 (2 ^ e + 1))
    (h : (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) =
      d * ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1)))) : False := by
  have hdodd : Odd d := hd ▸ odd_gcd_three _
  have hA : Odd ((2 ^ e) ^ 2 - 1) := by
    have := odd_two_pow_sub_one' (m := e * 2) (by omega)
    rwa [pow_mul] at this
  have hB : Odd ((2 ^ e) ^ 3 + 1) := by
    have := odd_two_pow_add_one' (m := e * 3) (by omega)
    rwa [pow_mul] at this
  have hC : Odd (2 ^ (2 * n) - 1) := odd_two_pow_sub_one' (by omega)
  have hD : Odd ((2 ^ (2 * n)) ^ 2 - 1) := by
    have := odd_two_pow_sub_one' (m := 2 * n * 2) (by omega)
    rwa [pow_mul] at this
  have h3 : 3 * e = 4 * n := by
    refine even_exp_generic (M := ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1))
      (m := (2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1)) (d := d) (hA.mul hB) (hC.mul hD)
      hdodd ?_
    have e2 : (2 ^ (2 * n)) ^ 2 = 2 ^ (4 * n) := by rw [← pow_mul]; congr 1; ring
    rw [h]
    rw [e2]
  obtain ⟨j, hj1, hj2⟩ : ∃ j, e = 4 * j ∧ n = 3 * j := ⟨e / 4, by omega, by omega⟩
  subst hj1 hj2
  have hx : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQ : 2 ^ (4 * j) = (2 ^ j) ^ 4 := by rw [← pow_mul, mul_comm]
  have hy : 2 ^ (2 * (3 * j)) = (2 ^ j) ^ 6 := by rw [← pow_mul]; congr 1; ring
  have hdv : d = 1 := by rw [hd, show 4 * j = 2 * (2 * j) by ring, gcd_three_add_eq]
  rw [hQ, hy, hdv] at h
  exact alg_U3_S hx h

private theorem even_L3_G {e n d : ℕ} (he : 1 ≤ e) (hn : 2 ≤ n) (hd : d = Nat.gcd 3 (2 ^ e - 1))
    (h : (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) =
      d * ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1)))) : False := by
  have hdodd : Odd d := hd ▸ odd_gcd_three _
  have hA : Odd ((2 ^ e) ^ 2 - 1) := by
    have := odd_two_pow_sub_one' (m := e * 2) (by omega)
    rwa [pow_mul] at this
  have hB : Odd ((2 ^ e) ^ 3 - 1) := by
    have := odd_two_pow_sub_one' (m := e * 3) (by omega)
    rwa [pow_mul] at this
  have hC : Odd (2 ^ (2 * n) - 1) := odd_two_pow_sub_one' (by omega)
  have hD : Odd ((2 ^ (2 * n)) ^ 3 - 1) := by
    have := odd_two_pow_sub_one' (m := 2 * n * 3) (by omega)
    rwa [pow_mul] at this
  have h3 : 3 * e = 6 * n := by
    refine even_exp_generic (M := ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1))
      (m := ((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1)) (d := d) (hA.mul hB) (hD.mul hC)
      hdodd ?_
    have e2 : (2 ^ (2 * n)) ^ 3 = 2 ^ (6 * n) := by rw [← pow_mul]; congr 1; ring
    rw [h]
    rw [e2]
  obtain rfl : e = 2 * n := by omega
  have hy := sixteen_le_two_pow_two_mul hn
  have hdv : d = 3 := by rw [hd, gcd_three_sub_eq]
  rw [hdv] at h
  exact alg_L3_G hy h

private theorem even_U3_G {e n d : ℕ} (he : 1 ≤ e) (hn : 2 ≤ n) (hd : d = Nat.gcd 3 (2 ^ e + 1))
    (h : (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) =
      d * ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1)))) : False := by
  have hdodd : Odd d := hd ▸ odd_gcd_three _
  have hA : Odd ((2 ^ e) ^ 2 - 1) := by
    have := odd_two_pow_sub_one' (m := e * 2) (by omega)
    rwa [pow_mul] at this
  have hB : Odd ((2 ^ e) ^ 3 + 1) := by
    have := odd_two_pow_add_one' (m := e * 3) (by omega)
    rwa [pow_mul] at this
  have hC : Odd (2 ^ (2 * n) - 1) := odd_two_pow_sub_one' (by omega)
  have hD : Odd ((2 ^ (2 * n)) ^ 3 - 1) := by
    have := odd_two_pow_sub_one' (m := 2 * n * 3) (by omega)
    rwa [pow_mul] at this
  have h3 : 3 * e = 6 * n := by
    refine even_exp_generic (M := ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1))
      (m := ((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1)) (d := d) (hA.mul hB) (hD.mul hC)
      hdodd ?_
    have e2 : (2 ^ (2 * n)) ^ 3 = 2 ^ (6 * n) := by rw [← pow_mul]; congr 1; ring
    rw [h]
    rw [e2]
  obtain rfl : e = 2 * n := by omega
  have hy := sixteen_le_two_pow_two_mul hn
  have hdv : d = 1 := by rw [hd, gcd_three_add_eq]
  rw [hdv] at h
  exact alg_U3_G hy h

private theorem prime_pow_cases {Q : ℕ} (hQ : ∃ r e : ℕ, r.Prime ∧ 1 ≤ e ∧ Q = r ^ e) :
    (∃ e : ℕ, 1 ≤ e ∧ Q = 2 ^ e) ∨ ∃ t : ℕ, 1 ≤ t ∧ Q = 2 * t + 1 := by
  obtain ⟨r, e, hr, he, rfl⟩ := hQ
  by_cases hr2 : r = 2
  · exact Or.inl ⟨e, he, by rw [hr2]⟩
  · refine Or.inr ?_
    have hodd : Odd r := hr.odd_of_ne_two hr2
    have hr3 : 3 ≤ r := by
      have := hr.two_le
      rcases hodd with ⟨k, hk⟩
      omega
    obtain ⟨t, ht⟩ := hodd.pow (n := e)
    have : 3 ≤ r ^ e := le_trans hr3 (Nat.le_self_pow (by omega) r)
    exact ⟨t, by omega, ht⟩

private theorem gcd_three_le (m : ℕ) : Nat.gcd 3 m ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 m)

theorem no_psl3_sp4 {Q n : ℕ} (hn : 2 ≤ n) (hQ : ∃ r e : ℕ, r.Prime ∧ 1 ≤ e ∧ Q = r ^ e) :
    Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ≠
      Nat.gcd 3 (Q - 1) *
        ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1))) := by
  intro h
  rcases prime_pow_cases hQ with ⟨e, he, rfl⟩ | ⟨t, ht, rfl⟩
  · exact even_L3_S he hn rfl h
  · exact no_psl3_sp4_odd hn ht (gcd_three_le _) h

theorem no_psu3_sp4 {Q n : ℕ} (hn : 2 ≤ n) (hQ : ∃ r e : ℕ, r.Prime ∧ 1 ≤ e ∧ Q = r ^ e) :
    Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) ≠
      Nat.gcd 3 (Q + 1) *
        ((2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1))) := by
  intro h
  rcases prime_pow_cases hQ with ⟨e, he, rfl⟩ | ⟨t, ht, rfl⟩
  · exact even_U3_S he hn rfl h
  · exact no_psu3_sp4_odd hn ht (gcd_three_le _) h

theorem no_psl3_g2 {Q n : ℕ} (hn : 2 ≤ n) (hQ : ∃ r e : ℕ, r.Prime ∧ 1 ≤ e ∧ Q = r ^ e) :
    Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ≠
      Nat.gcd 3 (Q - 1) *
        ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1))) := by
  intro h
  rcases prime_pow_cases hQ with ⟨e, he, rfl⟩ | ⟨t, ht, rfl⟩
  · exact even_L3_G he hn rfl h
  · exact no_psl3_g2_odd hn ht (gcd_three_le _) h

theorem no_psu3_g2 {Q n : ℕ} (hn : 2 ≤ n) (hQ : ∃ r e : ℕ, r.Prime ∧ 1 ≤ e ∧ Q = r ^ e) :
    Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) ≠
      Nat.gcd 3 (Q + 1) *
        ((2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1))) := by
  intro h
  rcases prime_pow_cases hQ with ⟨e, he, rfl⟩ | ⟨t, ht, rfl⟩
  · exact even_U3_G he hn rfl h
  · exact no_psu3_g2_odd hn ht (gcd_three_le _) h

end CFSG.Quasithin.A318Excl
