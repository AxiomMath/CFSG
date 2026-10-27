module

public import CFSG.Quasithin.Vol2.Ch10SecA312C3

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312C

theorem not_pow_succ_dvd {r k N : ℕ} (hr : r.Prime) (hN : N ≠ 0) (h : N.factorization r ≤ k) :
    ¬ r ^ (k + 1) ∣ N := fun hd => by
  have := (hr.pow_dvd_iff_le_factorization hN).mp hd
  omega

theorem factorization_mul_apply {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (r : ℕ) :
    (a * b).factorization r = a.factorization r + b.factorization r := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

theorem factorization_eq_zero_of_not_dvd' {a r : ℕ} (h : ¬ r ∣ a) : a.factorization r = 0 :=
  Nat.factorization_eq_zero_of_not_dvd h

theorem factorization_le_of_dvd {N M : ℕ} (h : N ∣ M) (hM : M ≠ 0) (r : ℕ) :
    N.factorization r ≤ M.factorization r :=
  (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hM h) hM).mpr h r

variable {Y : Type} [Group Y]

theorem card_dvd_of_isPSL2 {p : ℕ} (h : IsPSL 2 p 1 Y) : Nat.card Y ∣ p * (p ^ 2 - 1) := by
  rw [card_of_isPSL h]
  simp only [pow_one, show (2 * (2 - 1) / 2 : ℕ) = 1 from rfl, Finset.Icc_self,
    Finset.prod_singleton]
  exact Nat.div_dvd_of_dvd ((Nat.gcd_dvd_right 2 (p - 1)).trans
    ((Nat.sub_one_dvd_pow_sub_one p 2).mul_left p))

theorem card_dvd_of_isPSL2_sq {p : ℕ} (h : IsPSL 2 p 2 Y) :
    Nat.card Y ∣ p ^ 2 * ((p ^ 2 - 1) * (p ^ 2 + 1)) := by
  rw [card_of_isPSL h]
  have hfac : (p ^ 2) ^ 2 - 1 = (p ^ 2 - 1) * (p ^ 2 + 1) := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · zify [Nat.one_le_pow 2 p hp, Nat.one_le_pow 2 (p ^ 2) (by positivity)]; ring
  simp only [pow_one, show (2 * (2 - 1) / 2 : ℕ) = 1 from rfl, Finset.Icc_self,
    Finset.prod_singleton, hfac]
  exact Nat.div_dvd_of_dvd ((Nat.gcd_dvd_right 2 (p ^ 2 - 1)).trans
    ((dvd_mul_right (p ^ 2 - 1) (p ^ 2 + 1)).mul_left _))

theorem card_dvd_of_isPSL3 {p : ℕ} (h : IsPSL 3 p 1 Y) :
    Nat.card Y ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
  rw [card_of_isPSL h]
  simp only [pow_one, show (3 * (3 - 1) / 2 : ℕ) = 3 from rfl,
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (show (2 : ℕ) ≠ 3 by norm_num)]
  exact Nat.div_dvd_of_dvd ((Nat.gcd_dvd_right 3 (p - 1)).trans
    ((Nat.sub_one_dvd_pow_sub_one p 3).trans ((dvd_mul_left _ _).mul_left _)))

theorem card_mul_gcd_of_isPSL2 {p : ℕ} (h : IsPSL 2 p 1 Y) :
    Nat.card Y * Nat.gcd 2 (p - 1) = p * (p ^ 2 - 1) := by
  rw [card_of_isPSL h]
  simp only [pow_one, show (2 * (2 - 1) / 2 : ℕ) = 1 from rfl, Finset.Icc_self,
    Finset.prod_singleton]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right 2 (p - 1)).trans
    ((Nat.sub_one_dvd_pow_sub_one p 2).mul_left p))

theorem sq_sub_one_eq (p : ℕ) : p ^ 2 - 1 = (p - 1) * (p + 1) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · zify [Nat.one_le_pow 2 p hp, hp]; ring

theorem cube_sub_one_eq (p : ℕ) : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · zify [Nat.one_le_pow 3 p hp, hp]; ring

theorem cube_add_one_eq (p : ℕ) : p ^ 3 + 1 = (p + 1) * (p ^ 2 - p + 1) := by
  have h : p ≤ p ^ 2 := by nlinarith
  zify [h]; ring

theorem psl2_sq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {B L : Type} [Group B] [Group L]
    [Finite L] (hB : IsPSL 2 p 1 B) (hL : IsPSL 2 p 2 L) :
    ∃ k, 1 ≤ k ∧ 3 ^ k ∣ Nat.card B ∧ ¬ 3 ^ (k + 1) ∣ Nat.card L := by
  have h3p : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  have hmod : p ^ 2 % 3 = 1 := by
    have : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases this with h | h <;> rw [h]
  have hp2 : 16 ≤ p ^ 2 := by nlinarith
  have hne : p ^ 2 - 1 ≠ 0 := by omega
  have h3 : 3 ∣ p ^ 2 - 1 := by omega
  refine ⟨(p ^ 2 - 1).factorization 3,
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hne).mp h3, ?_, ?_⟩
  · have h1 := card_mul_gcd_of_isPSL2 hB
    have h2 : 3 ^ (p ^ 2 - 1).factorization 3 ∣ Nat.card B * Nat.gcd 2 (p - 1) := by
      rw [h1]
      exact (Nat.ordProj_dvd _ _).mul_left p
    exact Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr
        (by norm_num)) |>.coprime_dvd_right (Nat.gcd_dvd_left 2 (p - 1))) h2
  · have hN : p ^ 2 * ((p ^ 2 - 1) * (p ^ 2 + 1)) ≠ 0 := by positivity
    refine not_pow_succ_dvd Nat.prime_three (Nat.card_pos.ne') ?_
    refine (factorization_le_of_dvd (card_dvd_of_isPSL2_sq hL) hN 3).trans ?_
    rw [factorization_mul_apply (by positivity) (by positivity),
      factorization_mul_apply hne (by positivity),
      factorization_eq_zero_of_not_dvd' (fun h => h3p (Nat.prime_three.dvd_of_dvd_pow h)),
      factorization_eq_zero_of_not_dvd' (show ¬ 3 ∣ p ^ 2 + 1 by omega)]
    omega

end CFSG.Quasithin.Vol2.Ch10.A312C
