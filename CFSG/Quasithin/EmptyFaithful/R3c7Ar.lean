module

public import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.R3c7

open CFSG.RankThree.PartTwo.KFacts.OddChar

theorem mul_sq_sub_one_lt {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) :
    x * (x ^ 2 - 1) < y * (y ^ 2 - 1) := by
  have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  have h2 : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2]
  have hxy' : (x : ℤ) < y := by exact_mod_cast hxy
  have hx' : (1 : ℤ) ≤ x := by exact_mod_cast hx
  nlinarith [mul_pos (show (0 : ℤ) < (y : ℤ) - (x : ℤ) by linarith)
    (show (0 : ℤ) < (x : ℤ) + y by linarith), sq_nonneg ((x : ℤ) + y)]

theorem eq_of_mul_sq_sub_one_eq {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : x * (x ^ 2 - 1) = y * (y ^ 2 - 1)) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (mul_sq_sub_one_lt hx hlt).ne
  · exact heq
  · exact absurd h (mul_sq_sub_one_lt hy hgt).ne'

theorem two_pow_padicValNat_le_of_l2p {p N : ℕ} (hp : Odd p) (hp1 : 1 < p)
    (h : N * 2 = p * (p ^ 2 - 1)) : 2 ^ padicValNat 2 N ≤ p + 1 := by
  have h2 : p ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hp1 (j := 2) (by norm_num)
  have hN0 : N ≠ 0 := by
    rintro rfl
    have h0 : p * (p ^ 2 - 1) = 0 := by simpa using h.symm
    rcases Nat.mul_eq_zero.1 h0 with h0 | h0 <;> omega
  have hv : padicValNat 2 N + 1 = padicValNat 2 (p ^ 2 - 1) := by
    have e := congrArg (padicValNat 2) h
    rw [padicValNat.mul hN0 two_ne_zero, padicValNat.self one_lt_two] at e
    rw [e]
    have := padicValNat_odd_pow_mul hp 1 h2
    simpa using this
  have hle := two_pow_padicValNat_sq_sub_one_le hp hp1
  rw [← hv, pow_succ] at hle
  omega

theorem succ_pow_three_le_of_l2p {p N : ℕ} (hp7 : 7 ≤ p) (h : N * 2 = p * (p ^ 2 - 1)) :
    (p + 1) ^ 3 ≤ 4 * N := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h' : (N : ℤ) * 2 = p * (p ^ 2 - 1) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast [Nat.cast_sub h1] at this
    exact this
  have hp' : (7 : ℤ) ≤ p := by exact_mod_cast hp7
  zify
  nlinarith [mul_pos (show (0 : ℤ) < p by linarith) (show (0 : ℤ) < p - 6 by linarith),
    sq_nonneg ((p : ℤ) - 7)]

theorem two_pow_three_le_of_l2p {p N : ℕ} (hp : Odd p) (hp7 : 7 ≤ p)
    (h : N * 2 = p * (p ^ 2 - 1)) : 2 ^ (3 * padicValNat 2 N) ≤ 4 * N := by
  have h1 := two_pow_padicValNat_le_of_l2p hp (by omega) h
  rw [pow_mul']
  exact (Nat.pow_le_pow_left h1 3).trans (succ_pow_three_le_of_l2p hp7 h)

theorem pow_four_sub_one (p : ℕ) : p ^ 4 - 1 = (p ^ 2 + 1) * (p ^ 2 - 1) := by
  have := Nat.sq_sub_sq (p ^ 2) 1
  rw [← pow_mul] at this
  simpa using this

theorem two_pow_padicValNat_le_of_l2sq {p N : ℕ} (hp : Odd p) (hp1 : 1 < p)
    (h : N * 2 = p ^ 2 * (p ^ 4 - 1)) : 2 ^ padicValNat 2 N ≤ 2 * (p + 1) := by
  have h2 : p ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hp1 (j := 2) (by norm_num)
  have h4 : p ^ 2 + 1 ≠ 0 := by positivity
  have hN0 : N ≠ 0 := by
    rintro rfl
    have h0 : p ^ 2 * (p ^ 4 - 1) = 0 := by simpa using h.symm
    rw [pow_four_sub_one] at h0
    rcases Nat.mul_eq_zero.1 h0 with h0 | h0
    · exact absurd h0 (pow_ne_zero 2 (by omega))
    · rcases Nat.mul_eq_zero.1 h0 with h0 | h0 <;> omega
  have hp2 : padicValNat 2 (p ^ 2 + 1) = 1 := by
    obtain ⟨k, rfl⟩ := hp
    have : (2 * k + 1) ^ 2 + 1 = 4 * (k * k + k) + 2 := by ring
    exact padicValNat_eq_one_of_mod_four (by omega)
  have hv : padicValNat 2 N + 1 = padicValNat 2 (p ^ 2 - 1) + 1 := by
    have e := congrArg (padicValNat 2) h
    rw [padicValNat.mul hN0 two_ne_zero, padicValNat.self one_lt_two, pow_four_sub_one,
      padicValNat_odd_pow_mul hp 2 (Nat.mul_ne_zero h4 h2), padicValNat.mul h4 h2, hp2] at e
    omega
  have hle := two_pow_padicValNat_sq_sub_one_le hp hp1
  have hν : padicValNat 2 N = padicValNat 2 (p ^ 2 - 1) := by omega
  rw [hν]
  exact hle

theorem eight_succ_pow_three_lt_of_l2sq {p N : ℕ} (hp5 : 5 ≤ p) (h : N * 2 = p ^ 2 * (p ^ 4 - 1)) :
    8 * (p + 1) ^ 3 < N := by
  have h1 : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h' : (N : ℤ) * 2 = p ^ 2 * (p ^ 4 - 1) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast [Nat.cast_sub h1] at this
    exact this
  have hp' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
  zify
  have hp4 : (625 : ℤ) ≤ (p : ℤ) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 5) hp' 4]
  nlinarith [mul_pos (show (0 : ℤ) < p by linarith) (show (0 : ℤ) < p - 4 by linarith),
    pow_pos (show (0 : ℤ) < p by linarith) 2, pow_pos (show (0 : ℤ) < p by linarith) 3,
    pow_pos (show (0 : ℤ) < p by linarith) 4]

theorem two_pow_three_lt_of_l2sq {p N : ℕ} (hp : Odd p) (hp5 : 5 ≤ p)
    (h : N * 2 = p ^ 2 * (p ^ 4 - 1)) : 2 ^ (3 * padicValNat 2 N) < N := by
  have h1 := two_pow_padicValNat_le_of_l2sq hp (by omega) h
  rw [pow_mul']
  calc (2 ^ padicValNat 2 N) ^ 3 ≤ (2 * (p + 1)) ^ 3 := Nat.pow_le_pow_left h1 3
    _ = 8 * (p + 1) ^ 3 := by ring
    _ < N := eight_succ_pow_three_lt_of_l2sq hp5 h

theorem le_of_l2sq {p N : ℕ} (hp5 : 5 ≤ p) (h : N * 2 = p ^ 2 * (p ^ 4 - 1)) : 7800 ≤ N := by
  have h1 : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
  have h2 : 5 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp5 4
  have h3 : 5 ^ 2 * (5 ^ 4 - 1) ≤ p ^ 2 * (p ^ 4 - 1) :=
    Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
  omega

theorem le_of_mul_sq_sub_one_lt {p B : ℕ}
    (h : p * (p ^ 2 - 1) < (B + 1) * ((B + 1) ^ 2 - 1)) : p ≤ B := by
  by_contra hlt
  have h1 : B + 1 ≤ p := by omega
  have h2 : (B + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : (B + 1) * ((B + 1) ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
    Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
  omega

theorem false_of_l2two_l2p {f p N : ℕ} (hf : 2 ≤ f) (hN : N = 2 ^ f * ((2 ^ f) ^ 2 - 1))
    (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) (h : N * 2 = p * (p ^ 2 - 1)) : False := by
  have hp2 : p ≠ 2 := by omega
  set m : ℕ := 2 ^ f with hm
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hpm : ¬ p ∣ m := by
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hdvd : p ∣ m * ((m ^ 2 - 1) * 2) := by
    have : p ∣ N * 2 := ⟨p ^ 2 - 1, by rw [h]⟩
    rw [hN] at this
    simpa [mul_assoc] using this
  have h1 : p ∣ m ^ 2 - 1 := by
    have h2 := (hp.dvd_mul.1 hdvd).resolve_left hpm
    rcases hp.dvd_mul.1 h2 with h3 | h3
    · exact h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3) hp2
  have hfac : m ^ 2 - 1 = (m + 1) * (m - 1) := by
    have := Nat.sq_sub_sq m 1
    simpa using this
  have hle : p ≤ m + 1 := by
    rw [hfac] at h1
    rcases hp.dvd_mul.1 h1 with h3 | h3
    · exact Nat.le_of_dvd (by omega) h3
    · exact (Nat.le_of_dvd (by omega) h3).trans (by omega)
  have h4 : p * (p ^ 2 - 1) ≤ (m + 1) * ((m + 1) ^ 2 - 1) :=
    Nat.mul_le_mul hle (Nat.sub_le_sub_right (Nat.pow_le_pow_left hle 2) 1)
  rw [← h, hN] at h4
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hm2 : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  by_cases hm5 : 5 ≤ m
  · exfalso
    zify [hm1, hm2] at h4
    have hm' : (5 : ℤ) ≤ m := by exact_mod_cast hm5
    nlinarith [mul_pos (show (0 : ℤ) < m by linarith) (show (0 : ℤ) < (m : ℤ) + 1 by linarith),
      mul_pos (mul_pos (show (0 : ℤ) < m by linarith) (show (0 : ℤ) < (m : ℤ) + 1 by linarith))
        (show (0 : ℤ) < (m : ℤ) - 4 by linarith)]
  · have hm4' : m = 4 := by omega
    rw [hm4'] at hN
    have h120 : p * (p ^ 2 - 1) = 120 := by
      rw [← h, hN]
      norm_num
    have hp5 : p ≤ 5 := by
      apply le_of_mul_sq_sub_one_lt
      rw [h120]
      norm_num
    interval_cases p <;> omega

theorem eq_of_l2_orders {p p' N : ℕ} (hp : 1 ≤ p) (hp' : 1 ≤ p') (h : N * 2 = p * (p ^ 2 - 1))
    (h' : N * 2 = p' * (p' ^ 2 - 1)) : p = p' :=
  eq_of_mul_sq_sub_one_eq hp hp' (h.symm.trans h')

theorem false_of_l2p_small {N p : ℕ} (hN : N = 360 ∨ N = 2520 ∨ N = 5616) (hp : p.Prime)
    (h : N * 2 = p * (p ^ 2 - 1)) : False := by
  rcases hN with rfl | rfl | rfl
  · have hp9 : p ≤ 9 := le_of_mul_sq_sub_one_lt (B := 9) (by rw [← h]; norm_num)
    interval_cases p <;> first | omega | (revert hp; norm_num)
  · have hp17 : p ≤ 17 := le_of_mul_sq_sub_one_lt (B := 17) (by rw [← h]; norm_num)
    interval_cases p <;> omega
  · have hp22 : p ≤ 22 := le_of_mul_sq_sub_one_lt (B := 22) (by rw [← h]; norm_num)
    interval_cases p <;> omega

theorem mem_primeFactors_of_dvd_mul_two {N p : ℕ} (hN : N ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ N * 2) : p ∈ N.primeFactors := by
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  exact Nat.mem_primeFactors.2 ⟨hp, hcop.dvd_of_dvd_mul_right hd, hN⟩

theorem l2_spor_aux {N : ℕ} (S : Finset ℕ) (hS : N.primeFactors = S) (hN : N ≠ 0)
    (h1 : ∀ p ∈ S, N * 2 ≠ p * (p ^ 2 - 1)) (h2 : ∀ p ∈ S, N * 2 ≠ p ^ 2 * (p ^ 4 - 1)) :
    (∀ p : ℕ, p.Prime → p ≠ 2 → N * 2 ≠ p * (p ^ 2 - 1)) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → N * 2 ≠ p ^ 2 * (p ^ 4 - 1)) := by
  constructor
  · intro p hp hp2 h
    have hd : p ∣ N * 2 := ⟨p ^ 2 - 1, h⟩
    exact h1 p (hS ▸ mem_primeFactors_of_dvd_mul_two hN hp hp2 hd) h
  · intro p hp hp2 h
    have hd : p ∣ N * 2 := ⟨p * (p ^ 4 - 1), by rw [h]; ring⟩
    exact h2 p (hS ▸ mem_primeFactors_of_dvd_mul_two hN hp hp2 hd) h

@[expose] def IsSporOrder (N : ℕ) : Prop :=
  N = 7920 ∨ N = 95040 ∨ N = 443520 ∨ N = 10200960 ∨ N = 244823040 ∨ N = 604800 ∨
    N = 86775571046077562880 ∨ N = 44352000 ∨ N = 4030387200 ∨ N = 145926144000

theorem l2_spor_false {N : ℕ} (hN : IsSporOrder N) :
    (∀ p : ℕ, p.Prime → p ≠ 2 → N * 2 ≠ p * (p ^ 2 - 1)) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → N * 2 ≠ p ^ 2 * (p ^ 4 - 1)) := by
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact l2_spor_aux {2, 3, 5, 11} (by norm_num [Nat.primeFactors]) (by norm_num) (by decide)
      (by decide)
  · exact l2_spor_aux {2, 3, 5, 11} (by norm_num [Nat.primeFactors]) (by norm_num) (by decide)
      (by decide)
  · exact l2_spor_aux {2, 3, 5, 7, 11} (by norm_num [Nat.primeFactors]) (by norm_num) (by decide)
      (by decide)
  · exact l2_spor_aux {2, 3, 5, 7, 11, 23} (by norm_num [Nat.primeFactors]) (by norm_num)
      (by decide) (by decide)
  · exact l2_spor_aux {2, 3, 5, 7, 11, 23} (by norm_num [Nat.primeFactors]) (by norm_num)
      (by decide) (by decide)
  · exact l2_spor_aux {2, 3, 5, 7} (by norm_num [Nat.primeFactors]) (by norm_num) (by decide)
      (by decide)
  · exact l2_spor_aux {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} (by norm_num [Nat.primeFactors])
      (by norm_num) (by decide) (by decide)
  · exact l2_spor_aux {2, 3, 5, 7, 11} (by norm_num [Nat.primeFactors]) (by norm_num) (by decide)
      (by decide)
  · exact l2_spor_aux {2, 3, 5, 7, 17} (by norm_num [Nat.primeFactors]) (by norm_num) (by decide)
      (by decide)
  · exact l2_spor_aux {2, 3, 5, 7, 13, 29} (by norm_num [Nat.primeFactors]) (by norm_num)
      (by decide) (by decide)

end CFSG.Quasithin.R3c7
