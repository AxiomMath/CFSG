module

public import CFSG.Quasithin.Vol2.Ch11SecA02Arith
public import CFSG.Quasithin.Vol2.Ch11SecAKind

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

theorem odd_oSL2_arith {m : ℕ} (hm : 1 ≤ m) : Odd (oSL2 m) := odd_two_pow_sub_one (by omega)

theorem oSL2_lt_oSL2 {a b : ℕ} (h : a < b) : oSL2 a < oSL2 b := two_pow_sub_one_lt (by omega)

theorem eq_of_two_pow_mul_eq {a b m o : ℕ} (hm : Odd m) (ho : Odd o)
    (h : 2 ^ a * m = 2 ^ b * o) : m = o := by
  have hab := eq_of_two_pow_mul_odd hm ho h
  subst hab
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

theorem oSL2_ne {n c k : ℕ} (hc : c < oSL2 k) (hne : ∀ j < k, oSL2 j ≠ c) : oSL2 n ≠ c := by
  intro h
  rcases lt_or_ge n k with hn | hn
  · exact hne n hn h
  · rcases hn.lt_or_eq with hn | rfl
    · have := oSL2_lt_oSL2 hn
      omega
    · omega

theorem oSL2_eq_fifteen {n : ℕ} (h : oSL2 n = 15) : n = 2 := by
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp_all [oSL2]
  · have := oSL2_lt_oSL2 (show 2 < n by omega)
    simp only [oSL2] at this h
    omega

theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem eq_five_of_sl2 {p n b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n) (hb : n ≤ b)
    (h : p * (p ^ 2 - 1) = 2 ^ b * oSL2 n) : p = 5 ∧ n = 2 := by
  set x := 2 ^ n with hx
  have hx4 : 4 ≤ x := four_le_two_pow hn
  have hxb : x ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hfac : oSL2 n = (x - 1) * (x + 1) := two_pow_two_mul_sub_one n
  have hcop : Nat.Coprime p (2 ^ b) := (Nat.coprime_primes hp Nat.prime_two |>.mpr hp2).pow_right b
  have hdvd : p ∣ (x - 1) * (x + 1) := by
    rw [← hfac]
    exact hcop.dvd_of_dvd_mul_left ⟨p ^ 2 - 1, by rw [← h]⟩
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · omega
      · exact hk0
    have hm : p ^ 2 - 1 = 2 ^ b * (k * (x + 1)) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < p by omega)
      rw [h, hfac, hk]
      ring
    have hpx : p ≤ x - 1 := by rw [hk]; exact Nat.le_mul_of_pos_right p hk1
    have h1 : x * (x + 1) ≤ 2 ^ b * (k * (x + 1)) := by
      calc x * (x + 1) ≤ 2 ^ b * (x + 1) := Nat.mul_le_mul_right _ hxb
        _ ≤ 2 ^ b * (k * (x + 1)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hk1)
    have h2 : p ^ 2 ≤ (x - 1) ^ 2 := Nat.pow_le_pow_left hpx 2
    have h3 : (x - 1) ^ 2 + 1 ≤ x * (x + 1) := by
      have : x - 1 + 1 = x := by omega
      nlinarith
    omega
  · have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · omega
      · exact hk0
    have hm : p ^ 2 - 1 = 2 ^ b * ((x - 1) * k) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < p by omega)
      rw [h, hfac, hk]
      ring
    rcases hk1.lt_or_eq with hk2 | rfl
    · exfalso
      have h1 : 2 * p ≤ x + 1 := by
        rw [hk, mul_comm p k]
        exact Nat.mul_le_mul_right p hk2
      have h2 : x * ((x - 1) * 2) ≤ 2 ^ b * ((x - 1) * k) :=
        Nat.mul_le_mul hxb (Nat.mul_le_mul_left _ hk2)
      have h3 : x * ((x - 1) * 2) + 1 ≤ p ^ 2 := by
        have : p ^ 2 = 2 ^ b * ((x - 1) * k) + 1 := by omega
        linarith
      have h4 : (2 * p) ^ 2 ≤ (x + 1) ^ 2 := Nat.pow_le_pow_left h1 2
      have hx1 : 1 ≤ x := by omega
      zify [hx1] at h3 h4
      have hx4' : (4 : ℤ) ≤ x := by exact_mod_cast hx4
      nlinarith
    · rw [mul_one] at hk
      have ht : x = 2 * 2 ^ (n - 1) := by
        rw [hx, ← pow_succ']
        congr 1
        omega
      have h2n : 2 ^ (n + 1) = 4 * 2 ^ (n - 1) := by
        rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
        ring
      have hp5 : p ^ 2 - 1 = 2 ^ (n + 1) * (2 ^ (n - 1) + 1) := by
        rw [← hk, ht, h2n]
        have : 1 ≤ (2 * 2 ^ (n - 1) + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        zify [this]
        ring
      rw [hm, mul_one] at hp5
      have hodd1 : Odd (x - 1) := odd_two_pow_sub_one (by omega)
      have hodd2 : Odd (2 ^ (n - 1) + 1) := by
        have : Even (2 ^ (n - 1)) := (Nat.even_pow' (by omega)).mpr even_two
        exact this.add_one
      have heq := eq_of_two_pow_mul_eq hodd1 hodd2 hp5
      have h2 : 2 ^ (n - 1) = 2 ^ 1 := by omega
      have hn2 : n - 1 = 1 := Nat.pow_right_injective le_rfl h2
      have hn2' : n = 2 := by omega
      refine ⟨?_, hn2'⟩
      subst hn2'
      norm_num at hx
      omega

theorem five_dvd_of_eleven_dvd {n : ℕ} (h : 11 ∣ oSL2 n) : 5 ∣ n := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h1 : ((oSL2 n : ℕ) : ZMod 11) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have h4 : (1 : ℕ) ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
  rw [oSL2, Nat.cast_sub h4, pow_mul, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h1
  have h2 : ((2 ^ 2 : ℕ) : ZMod 11) = 4 := by decide
  rw [h2] at h1
  have ho : orderOf (4 : ZMod 11) = 5 := orderOf_eq_prime (by decide) (by decide)
  rw [← ho]
  exact orderOf_dvd_of_pow_eq_one h1

theorem eleven_dvd_of_twentythree_dvd {n : ℕ} (h : 23 ∣ oSL2 n) : 11 ∣ n := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h1 : ((oSL2 n : ℕ) : ZMod 23) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have h4 : (1 : ℕ) ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
  rw [oSL2, Nat.cast_sub h4, pow_mul, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h1
  have h2 : ((2 ^ 2 : ℕ) : ZMod 23) = 4 := by decide
  rw [h2] at h1
  have ho : orderOf (4 : ZMod 23) = 11 := orderOf_eq_prime (by decide) (by decide)
  rw [← ho]
  exact orderOf_dvd_of_pow_eq_one h1

theorem oSL2_dvd_oSL2 {k n : ℕ} (h : k ∣ n) : oSL2 k ∣ oSL2 n := by
  obtain ⟨m, rfl⟩ := h
  have := Nat.sub_dvd_pow_sub_pow (2 ^ (2 * k)) 1 m
  rwa [one_pow, ← pow_mul, show 2 * k * m = 2 * (k * m) by ring] at this

theorem false_of_eleven_dvd {n : ℕ} (h11 : 11 ∣ oSL2 n) (h : oSL2 n ∣ 3 * Nat.factorial 22) :
    False := by
  have h31 : 31 ∣ oSL2 n := by
    have := oSL2_dvd_oSL2 (five_dvd_of_eleven_dvd h11)
    exact dvd_trans (by decide : 31 ∣ oSL2 5) this
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp (dvd_trans h31 h) with h3 | h3
  · norm_num at h3
  · exact absurd ((Nat.Prime.dvd_factorial (by norm_num)).mp h3) (by norm_num)

theorem false_of_twentythree_dvd {n : ℕ} (h23 : 23 ∣ oSL2 n)
    (h : oSL2 n ∣ Nat.factorial 24) : False := by
  have h89 : 89 ∣ oSL2 n := by
    have := oSL2_dvd_oSL2 (eleven_dvd_of_twentythree_dvd h23)
    exact dvd_trans (by decide : 89 ∣ oSL2 11) this
  exact absurd ((Nat.Prime.dvd_factorial (by norm_num)).mp (dvd_trans h89 h)) (by norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecA
