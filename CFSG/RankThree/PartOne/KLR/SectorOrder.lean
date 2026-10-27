module

public import CFSG.RankThree.Chevalley.SteinbergCFLargeReeSplitSylow

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.LieType.Ree CFSG.RankThree.LargeReeOrder CFSG.RankThree.Chevalley

theorem pow_factorization_dvd_of_not_dvd_cofactor {n M R p : ℕ} (hn : n = M * R) (hM : M ≠ 0)
    (hR : ¬ p ∣ R) : p ^ n.factorization p ∣ M := by
  have hR0 : R ≠ 0 := fun h => hR (h ▸ dvd_zero p)
  have hv : n.factorization p = M.factorization p := by
    rw [hn, Nat.factorization_mul hM hR0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hR, add_zero]
  rw [hv]
  exact Nat.ordProj_dvd M p

theorem prime_gt_three_not_dvd_smooth {p i j : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ p ∣ 2 ^ i * 3 ^ j := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
    omega

theorem not_dvd_cofactor_plus {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : 1 ≤ q)
    (hpq : p ∣ q + 1) :
    ¬ p ∣ q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  intro h
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hz : ((q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) : ℕ) :
      ℤ) = ((q : ℤ) ^ 23 - 4 * q ^ 22 + 9 * q ^ 21 - 15 * q ^ 20 + 20 * q ^ 19 - 23 * q ^ 18 +
        25 * q ^ 17 - 28 * q ^ 16 + 33 * q ^ 15 - 39 * q ^ 14 + 44 * q ^ 13 - 47 * q ^ 12 +
        48 * q ^ 11 - 48 * q ^ 10 + 48 * q ^ 9 - 48 * q ^ 8 + 48 * q ^ 7 - 48 * q ^ 6 +
        48 * q ^ 5 - 48 * q ^ 4 + 48 * q ^ 3 - 48 * q ^ 2 + 48 * q - 48) * ((q : ℤ) + 1) + 48 := by
    push_cast [Nat.cast_sub hq, Nat.cast_sub hq2, Nat.cast_sub hq4]
    ring
  have h1 : (p : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hpq
  have h2 := Int.natCast_dvd_natCast.2 h
  rw [hz] at h2
  have h3 : (p : ℤ) ∣ 48 := (dvd_add_right (dvd_mul_of_dvd_right h1 _)).1 h2
  have h4 : p ∣ 48 := by exact_mod_cast h3
  rw [show (48 : ℕ) = 2 ^ 4 * 3 ^ 1 by norm_num] at h4
  exact prime_gt_three_not_dvd_smooth hp hp3 h4

theorem not_dvd_cofactor_four {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : 1 ≤ q)
    (hpq0 : ¬ p ∣ q) (hpq : p ∣ q ^ 2 + 1) :
    ¬ p ∣ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  intro h
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hz : ((q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) : ℕ) :
      ℤ) = ((q : ℤ) ^ 20 - q ^ 19 - 3 * q ^ 18 + 4 * q ^ 17 + 4 * q ^ 16 - 8 * q ^ 15 -
        3 * q ^ 14 + 11 * q ^ 13 + q ^ 12 - 12 * q ^ 11 + 12 * q ^ 9 - 12 * q ^ 7 + 12 * q ^ 5 -
        12 * q ^ 3 + 12 * q) * ((q : ℤ) ^ 2 + 1) - 12 * q := by
    push_cast [Nat.cast_sub hq, Nat.cast_sub hq2, Nat.cast_sub hq4]
    ring
  have h1 : (p : ℤ) ∣ (q : ℤ) ^ 2 + 1 := by exact_mod_cast hpq
  have h2 := Int.natCast_dvd_natCast.2 h
  rw [hz] at h2
  have h3 : (p : ℤ) ∣ 12 * q := by
    have := (dvd_sub_right (dvd_mul_of_dvd_right h1 _)).1 h2
    exact (dvd_neg.1 (by simpa using this))
  have h4 : p ∣ 12 * q := by exact_mod_cast h3
  rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
  · rw [show (12 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num] at h5
    exact prime_gt_three_not_dvd_smooth hp hp3 h5
  · exact hpq0 h5

theorem pow_factorization_card_reeGamma_dvd_phi1 {a : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ (2 * a + 1) - 1) :
    p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ (2 ^ (2 * a + 1) - 1) ^ 2 := by
  rw [(large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1]
  set q := 2 ^ (2 * a + 1) with hqdef
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine pow_factorization_dvd_of_not_dvd_cofactor ?_ (pow_ne_zero 2 (by omega))
    (not_dvd_cofactor hp hp3 (by omega) hpq)
  ring

theorem pow_factorization_card_reeGamma_dvd_phi2 {a : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ (2 * a + 1) + 1) :
    p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ (2 ^ (2 * a + 1) + 1) ^ 2 := by
  rw [(large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1]
  set q := 2 ^ (2 * a + 1) with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  refine pow_factorization_dvd_of_not_dvd_cofactor ?_ (pow_ne_zero 2 (by omega))
    (not_dvd_cofactor_plus hp hp3 hq1 hpq)
  ring

theorem phi4_factor (a : ℕ) :
    (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) * (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) =
      (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : (2 ^ (a + 1)) ^ 2 = 2 * 2 ^ (2 * a + 1) := by
    rw [← pow_mul, ← pow_succ']
    congr 1
    omega
  set q := 2 ^ (2 * a + 1) with hq
  set t := 2 ^ (a + 1) with ht
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hle
  rw [hs] at hsq ⊢
  rw [Nat.add_sub_cancel_left]
  have h2 : t ^ 2 = 2 * (t + s) := hsq
  nlinarith [h2]

theorem dvd_phi4_cases {a p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1) :
    (p ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 ∧ ¬ p ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) ∨
      (p ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 ∧ ¬ p ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) := by
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdiff : 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 =
      (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) + 2 ^ (a + 1) * 2 := by
    omega
  have hboth : p ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 →
      p ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 → False := by
    intro h1 h2
    rw [hdiff] at h1
    have h3 : p ∣ 2 ^ (a + 1) * 2 := (Nat.dvd_add_right h2).1 h1
    rw [← pow_succ] at h3
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
    omega
  rw [← phi4_factor a] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h2
  · exact Or.inl ⟨h1, fun h2 => hboth h1 h2⟩
  · exact Or.inr ⟨h2, fun h1 => hboth h1 h2⟩

theorem pow_factorization_card_reeGamma_dvd_four {a : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1) :
    p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣ ((2 ^ (2 * a + 1)) ^ 2 + 1) ^ 2 := by
  rw [(large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1]
  set q := 2 ^ (2 * a + 1) with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hpq0 : ¬ p ∣ q := fun h => by
    have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow h)
    omega
  refine pow_factorization_dvd_of_not_dvd_cofactor ?_ (pow_ne_zero 2 (by omega))
    (not_dvd_cofactor_four hp hp3 hq1 hpq0 hpq)
  ring

theorem pow_factorization_card_reeGamma_dvd_phi4p {a : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) :
    p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣
      (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) ^ 2 := by
  have hdvd : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    rw [← phi4_factor a]
    exact Dvd.dvd.mul_right hpq _
  have hnd : ¬ p ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
    rcases dvd_phi4_cases hp hp3 hdvd with h | h
    · exact h.2
    · exact fun h' => h.2 hpq
  have h1 := pow_factorization_card_reeGamma_dvd_four hK hp hp3 hdvd
  rw [← phi4_factor a, mul_pow] at h1
  exact (Nat.Coprime.pow _ 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).dvd_of_dvd_mul_right h1

theorem pow_factorization_card_reeGamma_dvd_phi4m {a : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) :
    p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣
      (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) ^ 2 := by
  have hdvd : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    rw [← phi4_factor a]
    exact Dvd.dvd.mul_left hpq _
  have hnd : ¬ p ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
    rcases dvd_phi4_cases hp hp3 hdvd with h | h
    · exact fun h' => h.2 hpq
    · exact h.2
  have h1 := pow_factorization_card_reeGamma_dvd_four hK hp hp3 hdvd
  rw [← phi4_factor a, mul_pow] at h1
  exact (Nat.Coprime.pow _ 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).dvd_of_dvd_mul_left h1

end CFSG.RankThree.PartOne.KLR
