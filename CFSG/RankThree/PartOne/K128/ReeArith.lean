module

public import CFSG.RankThree.PartOne.KF.F128Order

public section

namespace CFSG.RankThree.PartOne.K128

section Int

variable {p : ℕ}

theorem not_dvd_cofactor_six_int (hp : p.Prime) (hp5 : 5 ≤ p) {x : ℤ}
    (h : (p : ℤ) ∣ x ^ 2 - x + 1) :
    ¬ (p : ℤ) ∣ x ^ 12 * (x - 1) ^ 2 * (x + 1) ^ 2 * (x ^ 2 + 1) ^ 2 * (x ^ 4 - x ^ 2 + 1) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsmall : ∀ m : ℤ, m = 1 ∨ m = 2 ∨ m = 3 → ¬ (p : ℤ) ∣ m := by
    intro m hm hd
    rcases hm with rfl | rfl | rfl
    · exact hpz.not_dvd_one hd
    · have : p ∣ 2 := by exact_mod_cast hd
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have : p ∣ 3 := by exact_mod_cast hd
      have := Nat.le_of_dvd (by norm_num) this
      omega
  have h0 : ¬ (p : ℤ) ∣ x := by
    intro hd
    refine hsmall 1 (Or.inl rfl) ?_
    have e : (1 : ℤ) = (x ^ 2 - x + 1) - x * (x - 1) := by ring
    rw [e]
    exact dvd_sub h (dvd_mul_of_dvd_left hd _)
  have h1 : ¬ (p : ℤ) ∣ x - 1 := by
    intro hd
    refine hsmall 1 (Or.inl rfl) ?_
    have e : (1 : ℤ) = (x ^ 2 - x + 1) - (x - 1) * x := by ring
    rw [e]
    exact dvd_sub h (dvd_mul_of_dvd_left hd _)
  have h2 : ¬ (p : ℤ) ∣ x + 1 := by
    intro hd
    refine hsmall 3 (Or.inr (Or.inr rfl)) ?_
    have e : (3 : ℤ) = (x ^ 2 - x + 1) - (x + 1) * (x - 2) := by ring
    rw [e]
    exact dvd_sub h (dvd_mul_of_dvd_left hd _)
  have h3 : ¬ (p : ℤ) ∣ x ^ 2 + 1 := by
    intro hd
    apply h0
    have e : x = (x ^ 2 + 1) - (x ^ 2 - x + 1) := by ring
    rw [e]
    exact dvd_sub hd h
  have h4 : ¬ (p : ℤ) ∣ x ^ 4 - x ^ 2 + 1 := by
    intro hd
    have e : (2 : ℤ) * (x - 1) = -((x ^ 4 - x ^ 2 + 1) - (x ^ 2 - x + 1) * (x ^ 2 + x - 1)) := by
      ring
    have h5 : (p : ℤ) ∣ 2 * (x - 1) := by
      rw [e]
      exact dvd_neg.2 (dvd_sub hd (dvd_mul_of_dvd_left h _))
    rcases hpz.dvd_or_dvd h5 with h6 | h6
    · exact hsmall 2 (Or.inr (Or.inl rfl)) h6
    · exact h1 h6
  intro hR
  rcases hpz.dvd_or_dvd hR with hR | hR
  · rcases hpz.dvd_or_dvd hR with hR | hR
    · rcases hpz.dvd_or_dvd hR with hR | hR
      · rcases hpz.dvd_or_dvd hR with hR | hR
        · exact h0 (hpz.dvd_of_dvd_pow hR)
        · exact h1 (hpz.dvd_of_dvd_pow hR)
      · exact h2 (hpz.dvd_of_dvd_pow hR)
    · exact h3 (hpz.dvd_of_dvd_pow hR)
  · exact h4 hR

theorem not_dvd_cofactor_12p_int (hp : p.Prime) (hp5 : 5 ≤ p) {x y : ℤ} (hy : y ^ 2 = 2 * x)
    (h : (p : ℤ) ∣ x ^ 2 + x + 1 + y * (x + 1)) :
    ¬ (p : ℤ) ∣ x ^ 12 * (x - 1) ^ 2 * (x + 1) ^ 2 * (x ^ 2 + 1) ^ 2 * (x ^ 2 - x + 1) *
      (x ^ 2 + x + 1 - y * (x + 1)) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hy' : y ^ 2 - 2 * x = 0 := by rw [hy]; ring
  have hsmall : ∀ m : ℤ, m = 2 ∨ m = 4 ∨ m = 6 → ¬ (p : ℤ) ∣ m := by
    intro m hm hd
    rcases hm with rfl | rfl | rfl
    · have : p ∣ 2 := by exact_mod_cast hd
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have h22 : (p : ℤ) ∣ 2 * 2 := by simpa using hd
      rcases hpz.dvd_or_dvd h22 with h' | h' <;>
      · have : p ∣ 2 := by exact_mod_cast h'
        have := Nat.le_of_dvd (by norm_num) this
        omega
    · have h23 : (p : ℤ) ∣ 2 * 3 := by simpa using hd
      rcases hpz.dvd_or_dvd h23 with h' | h'
      · have : p ∣ 2 := by exact_mod_cast h'
        have := Nat.le_of_dvd (by norm_num) this
        omega
      · have : p ∣ 3 := by exact_mod_cast h'
        have := Nat.le_of_dvd (by norm_num) this
        omega
  have h0 : ¬ (p : ℤ) ∣ x := by
    intro hd
    refine hsmall 2 (Or.inl rfl) ?_
    have e : (2 : ℤ) = (-2 * y + 2) * (x ^ 2 + x + 1 + y * (x + 1)) +
        (x + 2) * (y ^ 2 - 2 * x) + (2 * x * y + y ^ 2 + 2) * x := by ring
    rw [e, hy', mul_zero, add_zero]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right hd _)
  have h1 : ¬ (p : ℤ) ∣ x - 1 := by
    intro hd
    refine hsmall 2 (Or.inl rfl) ?_
    have e : (2 : ℤ) = (-4 * y + 6) * (x ^ 2 + x + 1 + y * (x + 1)) +
        (3 * x + 5) * (y ^ 2 - 2 * x) + (4 * x * y + y ^ 2 + 2 * y + 4) * (x - 1) := by ring
    rw [e, hy', mul_zero, add_zero]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right hd _)
  have h2 : ¬ (p : ℤ) ∣ x + 1 := by
    intro hd
    refine hsmall 2 (Or.inl rfl) ?_
    have e : (2 : ℤ) = 2 * (x ^ 2 + x + 1 + y * (x + 1)) +
        (x + 1) * (y ^ 2 - 2 * x) + (-y ^ 2 - 2 * y) * (x + 1) := by ring
    rw [e, hy', mul_zero, add_zero]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right hd _)
  have h3 : ¬ (p : ℤ) ∣ x ^ 2 + 1 := by
    intro hd
    refine hsmall 6 (Or.inr (Or.inr rfl)) ?_
    have e : (6 : ℤ) = (-2 * x * y + y ^ 2 - 2 * y) * (x ^ 2 + x + 1 + y * (x + 1)) +
        (-x * y + 3 * x - y) * (y ^ 2 - 2 * x) +
        (2 * x * y + y ^ 2 + 2 * y + 6) * (x ^ 2 + 1) := by ring
    rw [e, hy', mul_zero, add_zero]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right hd _)
  have h4 : ¬ (p : ℤ) ∣ x ^ 2 - x + 1 := by
    intro hd
    refine hsmall 2 (Or.inl rfl) ?_
    have e : (2 : ℤ) = (-2 * x * y + y ^ 2 + y - 2) * (x ^ 2 + x + 1 + y * (x + 1)) +
        (-x * y + x - y - 3) * (y ^ 2 - 2 * x) +
        (2 * x * y + y ^ 2 + y + 4) * (x ^ 2 - x + 1) := by ring
    rw [e, hy', mul_zero, add_zero]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right hd _)
  have h5 : ¬ (p : ℤ) ∣ x ^ 2 + x + 1 - y * (x + 1) := by
    intro hd
    refine hsmall 4 (Or.inr (Or.inl rfl)) ?_
    have e : (4 : ℤ) = (-y + 2) * (x ^ 2 + x + 1 + y * (x + 1)) +
        (2 * x + 2) * (y ^ 2 - 2 * x) + (y + 2) * (x ^ 2 + x + 1 - y * (x + 1)) := by ring
    rw [e, hy', mul_zero, add_zero]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right hd _)
  intro hR
  rcases hpz.dvd_or_dvd hR with hR | hR
  · rcases hpz.dvd_or_dvd hR with hR | hR
    · rcases hpz.dvd_or_dvd hR with hR | hR
      · rcases hpz.dvd_or_dvd hR with hR | hR
        · rcases hpz.dvd_or_dvd hR with hR | hR
          · exact h0 (hpz.dvd_of_dvd_pow hR)
          · exact h1 (hpz.dvd_of_dvd_pow hR)
        · exact h2 (hpz.dvd_of_dvd_pow hR)
      · exact h3 (hpz.dvd_of_dvd_pow hR)
    · exact h4 hR
  · exact h5 hR

theorem not_dvd_cofactor_12m_int (hp : p.Prime) (hp5 : 5 ≤ p) {x y : ℤ} (hy : y ^ 2 = 2 * x)
    (h : (p : ℤ) ∣ x ^ 2 + x + 1 - y * (x + 1)) :
    ¬ (p : ℤ) ∣ x ^ 12 * (x - 1) ^ 2 * (x + 1) ^ 2 * (x ^ 2 + 1) ^ 2 * (x ^ 2 - x + 1) *
      (x ^ 2 + x + 1 + y * (x + 1)) := by
  have h' := not_dvd_cofactor_12p_int hp hp5 (x := x) (y := -y) (by rw [neg_sq]; exact hy)
    (by convert h using 1; ring)
  convert h' using 3
  ring

end Int

section Nat

@[expose] def m12p (q t : ℕ) : ℕ := q ^ 2 + q + 1 + t * (q + 1)

@[expose] def m12m (q t : ℕ) : ℕ := q ^ 2 + q + 1 - t * (q + 1)

theorem t_mul_le {q t : ℕ} (ht : t ^ 2 = 2 * q) : t * (q + 1) ≤ q ^ 2 + q + 1 := by
  by_contra hlt
  have h1 : q ^ 2 + q + 1 < t * (q + 1) := not_le.1 hlt
  have h2 := Nat.mul_self_lt_mul_self h1
  have h3 : t * (q + 1) * (t * (q + 1)) = t ^ 2 * (q + 1) ^ 2 := by ring
  rw [h3, ht] at h2
  nlinarith [h2]

theorem m12_mul {q t : ℕ} (hq : 1 ≤ q) (ht : t ^ 2 = 2 * q) :
    m12p q t * m12m q t = q ^ 4 - q ^ 2 + 1 := by
  have htq := t_mul_le ht
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have ht' : (t : ℤ) ^ 2 = 2 * (q : ℤ) := by exact_mod_cast ht
  simp only [m12p, m12m]
  zify [htq, hq4]
  linear_combination (-((q : ℤ) + 1) ^ 2) * ht'

theorem not_dvd_cofactor_six {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (h : p ∣ q ^ 2 - q + 1) :
    ¬ p ∣ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1) := by
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  intro hn
  refine not_dvd_cofactor_six_int hp hp5 (x := (q : ℤ)) ?_ ?_
  · have := Int.natCast_dvd_natCast.2 h
    push_cast [Nat.cast_sub hq2] at this
    exact this
  · have := Int.natCast_dvd_natCast.2 hn
    push_cast [Nat.cast_sub hq, Nat.cast_sub hq4] at this
    exact this

theorem not_dvd_cofactor_12p {p q t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (ht : t ^ 2 = 2 * q) (h : p ∣ m12p q t) :
    ¬ p ∣ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      m12m q t := by
  have htq := t_mul_le ht
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have ht' : (t : ℤ) ^ 2 = 2 * (q : ℤ) := by exact_mod_cast ht
  intro hn
  refine not_dvd_cofactor_12p_int hp hp5 (x := (q : ℤ)) (y := (t : ℤ)) ht' ?_ ?_
  · have := Int.natCast_dvd_natCast.2 h
    push_cast [m12p] at this
    exact this
  · have := Int.natCast_dvd_natCast.2 hn
    push_cast [Nat.cast_sub hq, Nat.cast_sub hq2, m12m, Nat.cast_sub htq] at this
    exact this

theorem not_dvd_cofactor_12m {p q t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (ht : t ^ 2 = 2 * q) (h : p ∣ m12m q t) :
    ¬ p ∣ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      m12p q t := by
  have htq := t_mul_le ht
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have ht' : (t : ℤ) ^ 2 = 2 * (q : ℤ) := by exact_mod_cast ht
  intro hn
  refine not_dvd_cofactor_12m_int hp hp5 (x := (q : ℤ)) (y := (t : ℤ)) ht' ?_ ?_
  · have := Int.natCast_dvd_natCast.2 h
    push_cast [m12m, Nat.cast_sub htq] at this
    exact this
  · have := Int.natCast_dvd_natCast.2 hn
    push_cast [Nat.cast_sub hq, Nat.cast_sub hq2, m12p] at this
    exact this

theorem tsq (a : ℕ) : (2 ^ (a + 1)) ^ 2 = 2 * 2 ^ (2 * a + 1) := by
  rw [← pow_mul, show (a + 1) * 2 = (2 * a + 1) + 1 by ring, pow_succ]
  ring

end Nat

section PhiF4

@[expose] def phiF4 : ℕ → ℕ → ℕ
  | 1, Q => Q - 1
  | 2, Q => Q + 1
  | 4, Q => Q ^ 2 + 1
  | _, _ => 0

theorem phiF4_ne_zero {d Q : ℕ} (hd : d = 1 ∨ d = 2 ∨ d = 4) (hQ : 2 ≤ Q) : phiF4 d Q ≠ 0 := by
  rcases hd with rfl | rfl | rfl <;> simp only [phiF4] <;> omega

theorem cast_phiF4_pow {p q d : ℕ} [Fact p.Prime] (hq : 1 ≤ q) (hd : d = 1 ∨ d = 2 ∨ d = 4) :
    ((phiF4 d (q ^ p) : ℕ) : ZMod p) = ((phiF4 d q : ℕ) : ZMod p) := by
  have h1 : 1 ≤ q ^ p := Nat.one_le_pow _ _ hq
  have hf : ((q : ZMod p)) ^ p = q := ZMod.pow_card _
  rcases hd with rfl | rfl | rfl
  · simp only [phiF4]
    rw [Nat.cast_sub h1, Nat.cast_sub hq]
    push_cast
    rw [hf]
  · simp only [phiF4]
    push_cast
    rw [hf]
  · simp only [phiF4]
    push_cast
    rw [hf]

theorem dvd_phiF4_of_dvd_pow {p q d : ℕ} (hp : p.Prime) (hq : 1 ≤ q)
    (hd : d = 1 ∨ d = 2 ∨ d = 4) (h : p ∣ phiF4 d (q ^ p)) : p ∣ phiF4 d q := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rwa [← cast_phiF4_pow (p := p) hq hd]

theorem factorization_phiF4_pow {p q d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (hd : d = 1 ∨ d = 2 ∨ d = 4) (h : p ∣ phiF4 d q) :
    (phiF4 d (q ^ p)).factorization p = (phiF4 d q).factorization p + 1 := by
  have hp2 : p ≠ 2 := by omega
  rcases hd with rfl | rfl | rfl
  · simp only [phiF4] at h ⊢
    have := factorization_pow_sub_one hp hp2 hq hpq
    simpa [h] using this
  · simp only [phiF4] at h ⊢
    have := factorization_pow_add_one hp hp2 hpq
    simpa [h] using this
  · simp only [phiF4] at h ⊢
    have e : (q ^ p) ^ 2 = (q ^ 2) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e]
    have := factorization_pow_add_one hp hp2 (x := q ^ 2)
      (fun h' => hpq (hp.dvd_of_dvd_pow h'))
    simpa [h] using this

end PhiF4

end CFSG.RankThree.PartOne.K128
