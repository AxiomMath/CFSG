module

public import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith

public section

namespace CFSG.Quasithin.R3c6

open CFSG.RankThree.PartTwo.KFacts.OddChar Finset

@[expose] def ord3Num (s : Bool) (q : ℕ) : ℕ :=
  q ^ 3 * ((q ^ 2 - 1) * (if s then q ^ 3 - 1 else q ^ 3 + 1))

@[expose] def IsOddOrder (N : ℕ) : Prop :=
  ∃ (s : Bool) (p e : ℕ), p.Prime ∧ p ≠ 2 ∧ 1 ≤ e ∧
    Int.ModEq 3 ((p ^ e : ℕ) : ℤ) (if s then 1 else -1) ∧ N * 3 = ord3Num s (p ^ e)

theorem five_le_of_modEq {s : Bool} {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hmod : Int.ModEq 3 ((p ^ e : ℕ) : ℤ) (if s then 1 else -1)) : 5 ≤ p := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h3 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
    cases s
    · simp only [Bool.false_eq_true, ite_false] at hmod
      unfold Int.ModEq at hmod
      generalize 3 ^ e = Q at *
      omega
    · simp only [ite_true] at hmod
      unfold Int.ModEq at hmod
      generalize 3 ^ e = Q at *
      omega
  exact hp.five_le_of_ne_two_of_ne_three hp2 hp3

theorem two_pow_le_of_su3 {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q) {N g : ℕ}
    (hN : N * g = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) (hg : g ∣ 3) :
    2 ^ (8 * padicValNat 2 N) ≤ N ^ 3 := by
  have hq1 : 1 < q := by omega
  have h2 := pow_sub_one_ne_zero hq1 (j := 2) (by norm_num)
  have h3 : q ^ 3 + 1 ≠ 0 := by omega
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hg3 : g ≤ 3 := Nat.le_of_dvd (by norm_num) hg
  have hg2 : ¬ 2 ∣ g := fun h => absurd (h.trans hg) (by norm_num)
  have hS : 0 < q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
    Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (Nat.pos_of_ne_zero h2)) (by omega)
  have hN0 : N ≠ 0 := by rintro rfl; omega
  have hv : padicValNat 2 N = padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (q ^ 3 + 1) := by
    have h := congrArg (padicValNat 2) hN
    rw [padicValNat.mul hN0 hg0, padicValNat.eq_zero_of_not_dvd hg2, add_zero, mul_assoc,
      padicValNat_odd_pow_mul hq _ (Nat.mul_ne_zero h2 h3), padicValNat.mul h2 h3] at h
    exact h
  have hb : 2 ^ padicValNat 2 N ≤ 2 * (q + 1) ^ 2 := hv ▸ two_pow_padicValNat_su3_le hq hq1
  have : 2 ^ (8 * padicValNat 2 N) * g ^ 3 ≤ N ^ 3 * g ^ 3 :=
    calc 2 ^ (8 * padicValNat 2 N) * g ^ 3 ≤ (2 * (q + 1) ^ 2) ^ 8 * 27 := by
          rw [pow_mul']
          exact Nat.mul_le_mul (Nat.pow_le_pow_left hb 8)
            (by calc g ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left hg3 3
                  _ = 27 := by norm_num)
      _ ≤ (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) ^ 3 := by rw [mul_comm]; exact poly_su3 hq5
      _ = N ^ 3 * g ^ 3 := by rw [← hN, mul_pow]
  exact Nat.le_of_mul_le_mul_right this (pow_pos (Nat.pos_of_ne_zero hg0) 3)

theorem IsOddOrder.two_pow_le {N : ℕ} (h : IsOddOrder N) :
    2 ^ (8 * padicValNat 2 N) ≤ N ^ 3 := by
  obtain ⟨s, p, e, hp, hp2, he, hmod, hN⟩ := h
  have hp5 := five_le_of_modEq hp hp2 he hmod
  have hq5 : 5 ≤ p ^ e := hp5.trans (Nat.le_self_pow (by omega) p)
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  cases s
  · simp only [Bool.false_eq_true, ite_false] at hmod hN
    unfold ord3Num at hN
    simp only [Bool.false_eq_true, ite_false] at hN
    exact two_pow_le_of_su3 hodd hq5 (g := 3) (by rw [hN]; ring) (dvd_refl 3)
  · simp only [ite_true] at hmod hN
    unfold ord3Num at hN
    simp only [ite_true] at hN
    have hq3 : 3 ≤ p ^ e := by omega
    have h3 : 3 ∣ p ^ e - 1 := by
      unfold Int.ModEq at hmod
      generalize p ^ e = Q at *
      omega
    refine two_pow_le_of_mul_eq_slOrd hodd hq3 (n := 3) (g := 3) le_rfl ?_ h3
    rw [hN]
    have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
    rw [hI, Finset.prod_pair (by norm_num)]

theorem padicValNat_eq_of_mul_odd {N g r a : ℕ} (hg : Odd g) (hr : Odd r)
    (h : N * g = 2 ^ a * r) : padicValNat 2 N = a := by
  have hr0 : r ≠ 0 := hr.pos.ne'
  have hg0 : g ≠ 0 := hg.pos.ne'
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hr0 h.symm
  have h' := congrArg (padicValNat 2) h
  rw [padicValNat.mul hN0 hg0, padicValNat.mul (pow_ne_zero _ two_ne_zero) hr0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hg.not_two_dvd_nat,
    padicValNat.eq_zero_of_not_dvd hr.not_two_dvd_nat] at h'
  omega

theorem IsOddOrder.false_of_two_adic {N a : ℕ} (h : IsOddOrder N) (hν : padicValNat 2 N = a)
    (hlt : N ^ 3 < 2 ^ (8 * a)) : False := by
  have h1 := h.two_pow_le
  rw [hν] at h1
  exact absurd (h1.trans_lt hlt) (lt_irrefl _)

theorem ord3Num_lt (s : Bool) {q : ℕ} (hq : 2 ≤ q) : ord3Num s q < 2 * q ^ 8 := by
  unfold ord3Num
  have h1 : q ^ 2 - 1 < q ^ 2 := Nat.sub_lt (by positivity) one_pos
  have h2 : (if s then q ^ 3 - 1 else q ^ 3 + 1) ≤ q ^ 3 + 1 := by split_ifs <;> omega
  calc q ^ 3 * ((q ^ 2 - 1) * (if s then q ^ 3 - 1 else q ^ 3 + 1))
      ≤ q ^ 3 * (q ^ 2 * (q ^ 3 + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h1.le h2)
    _ = q ^ 8 + q ^ 5 := by ring
    _ < 2 * q ^ 8 := by
      have : q ^ 5 < q ^ 8 := Nat.pow_lt_pow_right hq (by norm_num)
      omega

theorem IsOddOrder.exists_prime_power {N : ℕ} (h : IsOddOrder N) :
    ∃ p e : ℕ, p.Prime ∧ 5 ≤ p ∧ 1 ≤ e ∧ (p ^ e) ^ 3 ∣ N ∧ N < (p ^ e) ^ 8 := by
  obtain ⟨s, p, e, hp, hp2, he, hmod, hN⟩ := h
  have hp5 := five_le_of_modEq hp hp2 he hmod
  refine ⟨p, e, hp, hp5, he, ?_, ?_⟩
  · have h1 : (p ^ e) ^ 3 ∣ N * 3 := by
      rw [hN]
      exact dvd_mul_right _ _
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
    have h2 : Nat.Coprime ((p ^ e) ^ 3) 3 := (hcop.pow_left e).pow_left 3
    exact h2.dvd_of_dvd_mul_right h1
  · have hq2 : 2 ≤ p ^ e := (by omega : 2 ≤ p).trans (Nat.le_self_pow (by omega) p)
    have := ord3Num_lt s hq2
    omega

theorem IsOddOrder.exists_cube {N : ℕ} (h : IsOddOrder N) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ^ 3 ∣ N := by
  obtain ⟨p, e, hp, hp5, he, hd, -⟩ := h.exists_prime_power
  exact ⟨p, hp, hp5, (pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 3).trans hd⟩

theorem not_isOddOrder_of_cubeFree {N : ℕ} (h : ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ^ 3 ∣ N) :
    ¬ IsOddOrder N := by
  intro hN
  obtain ⟨p, hp, hp5, hd⟩ := hN.exists_cube
  exact h p hp hp5 hd

theorem notOddOrder_of_two_part {N g r a b : ℕ} (hg : Odd g) (hr : Odd r)
    (h : N * g = 2 ^ a * r) (hb : 2 ^ a * r < 2 ^ b) (hab : 3 * b ≤ 8 * a) : ¬ IsOddOrder N := by
  intro hN
  have hν := padicValNat_eq_of_mul_odd hg hr h
  have hN1 : N < 2 ^ b := lt_of_le_of_lt (h ▸ Nat.le_mul_of_pos_right N hg.pos) hb
  have h3 : N ^ 3 < 2 ^ (8 * a) :=
    calc N ^ 3 < (2 ^ b) ^ 3 := Nat.pow_lt_pow_left hN1 (by norm_num)
      _ = 2 ^ (3 * b) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (8 * a) := Nat.pow_le_pow_right (by norm_num) hab
  exact hN.false_of_two_adic hν h3

theorem ord3Num_pos (s : Bool) {q : ℕ} (hq : 2 ≤ q) : 0 < ord3Num s q := by
  unfold ord3Num
  have h4 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h8 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h3 : 0 < (if s then q ^ 3 - 1 else q ^ 3 + 1) := by
    split_ifs
    · omega
    · omega
  exact Nat.mul_pos (by omega) (Nat.mul_pos (by omega) h3)

theorem IsOddOrder.pos {N : ℕ} (h : IsOddOrder N) : 0 < N := by
  obtain ⟨s, p, e, hp, hp2, he, hmod, hN⟩ := h
  have hq2 : 2 ≤ p ^ e := (five_le_of_modEq hp hp2 he hmod).trans
    (Nat.le_self_pow (by omega) p) |>.trans' (by norm_num)
  have h1 := ord3Num_pos s hq2
  rw [← hN] at h1
  omega

end CFSG.Quasithin.R3c6
