module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepFieldTypes
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

namespace Item148Rank

theorem coprime_two_pow_of_odd148 {m : ℕ} (k : ℕ) (hm : Odd m) : Nat.Coprime (2 ^ k) m :=
  (Nat.coprime_two_left.mpr hm).pow_left k

theorem eq_of_two_pow_mul_odd148 {a b r s : ℕ} (hr : Odd r) (hs : Odd s)
    (h : 2 ^ a * r = 2 ^ b * s) : a = b := by
  have h2 := congrArg (padicValNat 2) h
  have hr2 : ¬ 2 ∣ r := by have := Nat.odd_iff.mp hr; omega
  have hs2 : ¬ 2 ∣ s := by have := Nat.odd_iff.mp hs; omega
  rwa [padicValNat.mul (by positivity) hr.pos.ne', padicValNat.mul (by positivity) hs.pos.ne',
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hr2,
    padicValNat.eq_zero_of_not_dvd hs2, add_zero, add_zero] at h2

theorem two_pow_le_of_dvd148 {k u : ℕ} (hk : 2 ≤ k) (hu : Even u) (hu0 : 0 < u)
    (h : 2 ^ k ∣ u ^ 2 * (u + 2) ∨ 2 ^ k ∣ u * (u + 2) ^ 2) : 2 ^ k ≤ 2 * (u + 2) ^ 2 := by
  obtain ⟨s, rfl⟩ := hu
  have hk2 : 2 ^ k = 4 * 2 ^ (k - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hk1 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rcases Nat.even_or_odd s with hs | hs
  ·
    have ht : Odd (s + 1) := hs.add_one
    rcases h with h | h
    · have h' : 2 * 2 ^ (k - 1) ∣ 2 * ((s + 1) * (s + s) ^ 2) := by
        rw [← hk1]
        convert h using 1
        ring
      have h3 : 2 ^ (k - 1) ∣ (s + s) ^ 2 :=
        (coprime_two_pow_of_odd148 (k - 1) ht).dvd_of_dvd_mul_left
          (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h')
      have h4 := Nat.le_of_dvd (by positivity) h3
      nlinarith
    · have h' : 4 * 2 ^ (k - 2) ∣ 4 * ((s + 1) ^ 2 * (s + s)) := by
        rw [← hk2]
        convert h using 1
        ring
      have h3 : 2 ^ (k - 2) ∣ s + s :=
        (coprime_two_pow_of_odd148 (k - 2) ht.pow).dvd_of_dvd_mul_left
          (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h')
      have h4 := Nat.le_of_dvd (by omega) h3
      nlinarith
  ·
    rcases h with h | h
    · have h' : 4 * 2 ^ (k - 2) ∣ 4 * (s ^ 2 * (s + s + 2)) := by
        rw [← hk2]
        convert h using 1
        ring
      have h3 : 2 ^ (k - 2) ∣ s + s + 2 :=
        (coprime_two_pow_of_odd148 (k - 2) hs.pow).dvd_of_dvd_mul_left
          (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h')
      have h4 := Nat.le_of_dvd (by omega) h3
      nlinarith
    · have h' : 2 * 2 ^ (k - 1) ∣ 2 * (s * (s + s + 2) ^ 2) := by
        rw [← hk1]
        convert h using 1
        ring
      have h3 : 2 ^ (k - 1) ∣ (s + s + 2) ^ 2 :=
        (coprime_two_pow_of_odd148 (k - 1) hs).dvd_of_dvd_mul_left
          (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h')
      have h4 := Nat.le_of_dvd (by positivity) h3
      nlinarith

theorem succ_sq_sub_one148 (u : ℕ) : (u + 1) ^ 2 - 1 = u * (u + 2) := by
  have : (u + 1) ^ 2 = u * (u + 2) + 1 := by ring
  omega

theorem succ_cube_sub_one148 (u : ℕ) : (u + 1) ^ 3 - 1 = u * (u ^ 2 + 3 * u + 3) := by
  have : (u + 1) ^ 3 = u * (u ^ 2 + 3 * u + 3) + 1 := by ring
  omega

theorem mul_le_pow_five148 (q : ℕ) :
    (q ^ 2 - 1) * (q ^ 3 - 1) ≤ q ^ 5 ∧ (q ^ 2 - 1) * (q ^ 3 + 1) ≤ q ^ 5 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have h2 : (q ^ 2 - 1) + 1 = q ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)
  have h3 : (q ^ 3 - 1) + 1 = q ^ 3 := Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)
  have h23 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq (by norm_num)
  have h5 : q ^ 5 = q ^ 2 * q ^ 3 := by ring
  constructor
  · rw [h5]
    exact Nat.mul_le_mul (by omega) (by omega)
  · rw [h5]
    nlinarith

theorem pow_five_le148 {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 5 ≤ 2 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
  obtain ⟨u, rfl⟩ : ∃ u, Q = u + 2 := ⟨Q - 2, by omega⟩
  have h2 : (u + 2) ^ 2 - 1 = u ^ 2 + 4 * u + 3 := by
    have : (u + 2) ^ 2 = u ^ 2 + 4 * u + 3 + 1 := by ring
    omega
  have h3 : (u + 2) ^ 3 - 1 = u ^ 3 + 6 * u ^ 2 + 12 * u + 7 := by
    have : (u + 2) ^ 3 = u ^ 3 + 6 * u ^ 2 + 12 * u + 7 + 1 := by ring
    omega
  rw [h2, h3]
  nlinarith [sq_nonneg u, pow_pos (show 0 < u + 1 by omega) 3]

theorem false_of_card_eq_odd148 {n N Q g : ℕ} (hn : 1 ≤ n)
    (hq : 3 * N = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ∨
      3 * N = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)))
    (hQ : Odd Q) (hQ3 : 3 ≤ Q) (hg : g ∣ 3)
    (hN : N * g = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ∨
      N * g = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1))) : False := by
  set q := 2 ^ n with hqdef
  have hq2 : 2 ≤ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hg3 : g ≤ 3 := Nat.le_of_dvd (by norm_num) hg
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hg (by norm_num)
  have h3N : 3 * N ≤ q ^ 8 := by
    obtain ⟨h1, h2⟩ := mul_le_pow_five148 q
    rcases hq with h | h <;> rw [h, show q ^ 8 = q ^ 3 * q ^ 5 by ring] <;>
      exact Nat.mul_le_mul_left _ (by assumption)
  have hQ8 : Q ^ 8 ≤ 2 * (3 * N) := by
    have h5 := pow_five_le148 (show 2 ≤ Q by omega)
    have hR : Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ≤ N * g := by
      rcases hN with h | h
      · exact h.ge
      · rw [h]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have hNg : N * g ≤ 3 * N := by nlinarith
    calc Q ^ 8 = Q ^ 3 * Q ^ 5 := by ring
      _ ≤ Q ^ 3 * (2 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) := Nat.mul_le_mul_left _ h5
      _ = 2 * (Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) := by ring
      _ ≤ 2 * (3 * N) := by omega
  have hlt : 8 * Q < 9 * q := by
    by_contra hge
    push Not at hge
    have h1 : (9 * q) ^ 8 ≤ (8 * Q) ^ 8 := Nat.pow_le_pow_left hge 8
    rw [mul_pow, mul_pow] at h1
    have hq8 : 0 < q ^ 8 := by positivity
    nlinarith
  have hcop3 : Nat.Coprime (q ^ 3) 3 := by
    rw [hqdef, ← pow_mul]
    exact coprime_two_pow_of_odd148 _ (by decide)
  have hqN : q ^ 3 ∣ N := by
    refine hcop3.dvd_of_dvd_mul_left ?_
    rcases hq with h | h <;> rw [h] <;> exact Dvd.intro _ rfl
  have hcopQ : Nat.Coprime (q ^ 3) (Q ^ 3) := by
    rw [hqdef, ← pow_mul]
    exact coprime_two_pow_of_odd148 _ hQ.pow
  obtain ⟨u, rfl⟩ : ∃ u, Q = u + 1 := ⟨Q - 1, by omega⟩
  have hu : Even u := by
    obtain ⟨k, hk⟩ := hQ
    exact ⟨k, by omega⟩
  have hu0 : 0 < u := by omega
  have hdiv : 2 ^ (n * 3) ∣ u ^ 2 * (u + 2) ∨ 2 ^ (n * 3) ∣ u * (u + 2) ^ 2 := by
    rw [pow_mul, ← hqdef]
    rcases hN with h | h
    · left
      have h1 : q ^ 3 ∣ (u + 1) ^ 3 * ((u + 1) ^ 2 - 1) * ((u + 1) ^ 3 - 1) := by
        rw [mul_assoc, ← h]
        exact Dvd.dvd.mul_right hqN g
      have h2 : q ^ 3 ∣ (u ^ 2 * (u + 2)) * (u ^ 2 + 3 * u + 3) := by
        have h1' := hcopQ.dvd_of_dvd_mul_left (by rwa [mul_assoc] at h1)
        rwa [succ_sq_sub_one148, succ_cube_sub_one148,
          show u * (u + 2) * (u * (u ^ 2 + 3 * u + 3)) =
            u ^ 2 * (u + 2) * (u ^ 2 + 3 * u + 3) by ring] at h1'
      have hodd : Odd (u ^ 2 + 3 * u + 3) := by
        obtain ⟨k, rfl⟩ := hu
        exact ⟨2 * k ^ 2 + 3 * k + 1, by ring⟩
      rw [hqdef, ← pow_mul] at h2 ⊢
      exact (coprime_two_pow_of_odd148 _ hodd).dvd_of_dvd_mul_right h2
    · right
      have h1 : q ^ 3 ∣ (u + 1) ^ 3 * ((u + 1) ^ 2 - 1) * ((u + 1) ^ 3 + 1) := by
        rw [mul_assoc, ← h]
        exact Dvd.dvd.mul_right hqN g
      have h2 : q ^ 3 ∣ (u * (u + 2) ^ 2) * (u ^ 2 + u + 1) := by
        have h1' := hcopQ.dvd_of_dvd_mul_left (by rwa [mul_assoc] at h1)
        rwa [succ_sq_sub_one148, show (u + 1) ^ 3 + 1 = (u + 2) * (u ^ 2 + u + 1) by ring,
          show u * (u + 2) * ((u + 2) * (u ^ 2 + u + 1)) =
            u * (u + 2) ^ 2 * (u ^ 2 + u + 1) by ring] at h1'
      have hodd : Odd (u ^ 2 + u + 1) := by
        obtain ⟨k, rfl⟩ := hu
        exact ⟨2 * k ^ 2 + k, by ring⟩
      rw [hqdef, ← pow_mul] at h2 ⊢
      exact (coprime_two_pow_of_odd148 _ hodd).dvd_of_dvd_mul_right h2
  have hbound := two_pow_le_of_dvd148 (by omega) hu hu0 hdiv
  rw [pow_mul, ← hqdef] at hbound
  rcases Nat.lt_or_ge q 4 with h4 | h4
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with h2 | h3
    · omega
    ·
      have : 2 ∣ q := by rw [hqdef]; exact dvd_pow_self 2 (by omega)
      omega
  · have h1 : 8 * (u + 2) < 11 * q := by omega
    have h2 : 64 * (u + 2) ^ 2 < 121 * q ^ 2 := by nlinarith
    have h5 : 64 * q < 242 := by
      have : 64 * q * q ^ 2 < 242 * q ^ 2 := by nlinarith
      exact lt_of_mul_lt_mul_right this (Nat.zero_le _)
    omega

end Item148Rank

open Item148Rank

theorem kf148FieldChar_holds : KF148FieldChar := by
  intro X _ _ n hn _ hX p f _ hf hL
  have hp : p.Prime := Fact.out
  have hq : 3 * Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ∨
      3 * Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) := by
    rcases hX with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    · left
      have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
      rw [GaloisField.card 2 n (by omega), ← Nat.card_congr φ.toEquiv] at h
      rw [Nat.gcd_eq_left (show 3 ∣ 2 ^ n - 1 by omega)] at h
      rw [← h, mul_comm]
    · right
      have h := KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
      rw [← Nat.card_congr φ.toEquiv] at h
      rw [Nat.gcd_eq_left (show 3 ∣ 2 ^ n + 1 by omega)] at h
      rw [← h, mul_comm]
  obtain ⟨g, hg, hN⟩ : ∃ g, g ∣ 3 ∧
      (Nat.card X * g = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) ∨
        Nat.card X * g = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1))) := by
    rcases hL with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · refine ⟨Nat.gcd 3 (p ^ f - 1), Nat.gcd_dvd_left _ _, Or.inl ?_⟩
      have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p f)
      rw [GaloisField.card p f (by omega), ← Nat.card_congr φ.toEquiv] at h
      exact h
    · refine ⟨Nat.gcd 3 (p ^ f + 1), Nat.gcd_dvd_left _ _, Or.inr ?_⟩
      have h := KFacts.KS14.card_projSU_three_mul_gcd p f hf
      rw [← Nat.card_congr φ.toEquiv] at h
      exact h
  have hgodd : Odd g := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hg with rfl | rfl <;> decide
  rcases hp.eq_two_or_odd' with rfl | hpo
  ·
    refine ⟨rfl, ?_⟩
    have hodd1 : ∀ a : ℕ, 0 < a → Odd ((2 ^ n) ^ a - 1) ∧ Odd ((2 ^ n) ^ a + 1) := by
      intro a ha
      have he : Even ((2 ^ n) ^ a) := by
        rw [← pow_mul]
        exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩)
      have h1 : 1 ≤ (2 ^ n) ^ a := Nat.one_le_pow _ _ (by positivity)
      exact ⟨Nat.Even.sub_odd h1 he odd_one, he.add_one⟩
    have hodd2 : ∀ a : ℕ, 0 < a → Odd ((2 ^ f) ^ a - 1) ∧ Odd ((2 ^ f) ^ a + 1) := by
      intro a ha
      have he : Even ((2 ^ f) ^ a) := by
        rw [← pow_mul]
        exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩)
      have h1 : 1 ≤ (2 ^ f) ^ a := Nat.one_le_pow _ _ (by positivity)
      exact ⟨Nat.Even.sub_odd h1 he odd_one, he.add_one⟩
    obtain ⟨R1, hR1, hq'⟩ : ∃ R1, Odd R1 ∧ 3 * Nat.card X = 2 ^ (n * 3) * R1 := by
      rw [pow_mul]
      rcases hq with h | h
      · exact ⟨_, ((hodd1 2 (by norm_num)).1.mul (hodd1 3 (by norm_num)).1), h⟩
      · exact ⟨_, ((hodd1 2 (by norm_num)).1.mul (hodd1 3 (by norm_num)).2), h⟩
    obtain ⟨R2, hR2, hN'⟩ : ∃ R2, Odd R2 ∧ Nat.card X * g = 2 ^ (f * 3) * R2 := by
      rw [pow_mul]
      rcases hN with h | h
      · exact ⟨_, ((hodd2 2 (by norm_num)).1.mul (hodd2 3 (by norm_num)).1), h⟩
      · exact ⟨_, ((hodd2 2 (by norm_num)).1.mul (hodd2 3 (by norm_num)).2), h⟩
    have heq : 2 ^ (n * 3) * (R1 * g) = 2 ^ (f * 3) * (3 * R2) := by
      calc 2 ^ (n * 3) * (R1 * g) = 3 * Nat.card X * g := by rw [hq']; ring
        _ = 3 * (Nat.card X * g) := by ring
        _ = 2 ^ (f * 3) * (3 * R2) := by rw [hN']; ring
    have := eq_of_two_pow_mul_odd148 (hR1.mul hgodd) ((by decide : Odd 3).mul hR2) heq
    omega
  ·
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (by decide : ¬ Odd 2) hpo
      omega
    have hQ3 : 3 ≤ p ^ f := le_trans hp3 (Nat.le_self_pow (by omega) p)
    exact (false_of_card_eq_odd148 hn hq hpo.pow hQ3 hg hN).elim

theorem kf148FieldTypes_holds : KF148FieldTypes :=
  kf148FieldTypes_of_char kf148FieldChar_holds

end CFSG.RankThree.PartTwo.Sec14
