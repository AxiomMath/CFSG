module

public import CFSG.RankThree.PartOne.SEITZ6.G2MaxGold

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride CFSG.Monster.B.Recog.GoldschmidtArith
  CFSG.Monster.B.Recog.GoldschmidtArithOmega CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6 Matrix
open scoped MatrixGroups

@[expose] def d4Order (n : ℕ) : ℕ :=
  (2 ^ n) ^ 12 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1)

theorem d4Order_two : d4Order 2 = 2 ^ 24 * (3 ^ 4 * (5 ^ 2 * (7 ^ 2 * (13 ^ 2 * 241)))) := by
  norm_num [d4Order]

theorem psl2_small_check4 {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (h8 : (p ^ f) % 8 = 3 ∨ (p ^ f) % 8 = 5) (h60 : 60 ∣ p ^ f * ((p ^ f) ^ 2 - 1) / 2)
    (hdvd : p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∣ d4Order 2) : p ^ f * ((p ^ f) ^ 2 - 1) / 2 = 60 := by
  have hodd : (p ^ f) % 2 = 1 := by omega
  have h2 : 2 ∣ (p ^ f) ^ 2 - 1 := by
    have h : (p ^ f) ^ 2 % 2 = 1 := by
      rw [pow_two, Nat.mul_mod, hodd]
    have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hmN : p ^ f ∣ d4Order 2 := by
    refine Dvd.dvd.trans ?_ hdvd
    rw [Nat.mul_div_assoc _ h2]
    exact Dvd.intro _ rfl
  have hpN : p ∣ 2 ^ 24 * (3 ^ 4 * (5 ^ 2 * (7 ^ 2 * (13 ^ 2 * 241)))) := by
    rw [← d4Order_two]
    exact (dvd_pow_self p hf.ne').trans hmN
  have hp2 : p ≠ 2 := by
    rintro rfl
    simp at hodd
    omega
  have hplist : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 241 := by
    have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
      (Nat.prime_dvd_prime_iff_eq hp hq).1 h
    rcases (Nat.Prime.dvd_mul hp).1 hpN with h | h
    · exact absurd (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h)) hp2
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inl (hq 3 (by norm_num) (hp.dvd_of_dvd_pow h))
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inr (Or.inl (hq 5 (by norm_num) (hp.dvd_of_dvd_pow h)))
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) (hp.dvd_of_dvd_pow h))))
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 13 (by norm_num) (hp.dvd_of_dvd_pow h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hq 241 (by norm_num) h))))
  have hf4 : f ≤ 4 := by
    by_contra hf5
    push Not at hf5
    have hp5 : p ^ 5 ∣ d4Order 2 := (pow_dvd_pow p hf5).trans hmN
    rw [d4Order_two] at hp5
    rcases hplist with rfl | rfl | rfl | rfl | rfl <;> revert hp5 <;> norm_num
  have key : ∀ p ∈ [3, 5, 7, 13, 241], ∀ f ∈ [1, 2, 3, 4],
      p ^ f ∣ 2 ^ 24 * (3 ^ 4 * (5 ^ 2 * (7 ^ 2 * (13 ^ 2 * 241)))) →
      ((p ^ f) % 8 = 3 ∨ (p ^ f) % 8 = 5) → 60 ∣ p ^ f * ((p ^ f) ^ 2 - 1) / 2 →
      p ^ f * ((p ^ f) ^ 2 - 1) / 2 = 60 := by decide +kernel
  have hpl : p ∈ [3, 5, 7, 13, 241] := by
    rcases hplist with rfl | rfl | rfl | rfl | rfl <;> simp
  have hfl : f ∈ [1, 2, 3, 4] := by
    interval_cases f <;> simp
  rw [d4Order_two] at hmN
  exact key p hpl f hfl hmN h8 h60

theorem card_eq_of_carries1 {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Group K] [Finite K] (hK : goldschmidtSimpleType K)
    (h1 : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card K) (h2 : Nat.card K ∣ d4Order n)
    (h3 : (Nat.card K).factorization 2 = n) : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, h5, hq, ⟨e⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e⟩⟩
  ·
    have hcard : Nat.card K = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
      (Nat.card_congr e.toEquiv).trans (NearSolvable.card_psl2_even (by omega))
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      rw [← pow_mul]; exact odd_two_pow_sub_one (by omega)
    rw [hcard, factorization_two_pow_mul_odd f hodd] at h3
    subst h3
    exact hcard
  ·
    exact absurd (((three_dvd_two_pow_sq_sub_one n).mul_left (2 ^ n)).trans h1)
      (sz_not_three_dvd e)
  ·
    exfalso
    have h := NearSolvable.card_psu3_mul_gcd (p := f) (by omega)
    rw [← Nat.card_congr e.toEquiv] at h
    have hg : Odd (Nat.gcd 3 (2 ^ f + 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
    have hodd : Odd (((2 ^ f) ^ 2 - 1) * (2 ^ (f * 3) + 1)) := by
      rw [← pow_mul]
      exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_add_one (by omega))
    have hfac : (Nat.card K * Nat.gcd 3 (2 ^ f + 1)).factorization 2 =
        ((2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))).factorization 2 := by
      rw [h]
    rw [Nat.factorization_mul hpos hg.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hg.not_two_dvd_nat, add_zero, ← pow_mul,
      factorization_two_pow_mul_odd _ hodd] at hfac
    rw [hfac] at h3
    have hqq : 2 ^ n = (2 ^ f) ^ 3 := by rw [← h3, pow_mul]
    have hK1 : Nat.card K ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      rw [← h]; exact Dvd.intro _ rfl
    have h1' := h1.trans hK1
    rw [hqq] at h1'
    have hq1 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq3 : 1 ≤ (2 ^ f) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h1'' := Nat.dvd_of_mul_dvd_mul_left (pow_pos (by omega : 0 < 2 ^ f) 3) h1'
    rw [sq_sub_one_eq_mul (x := (2 ^ f) ^ 3) hq3, mul_comm ((2 ^ f) ^ 3 + 1)] at h1''
    have h1''' := Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < (2 ^ f) ^ 3 + 1) h1''
    exact not_dvd_cube_sub_one hq1 h1'''
  ·
    have h2f := psl2_odd_factorization hpo hf hq e
    rw [h2f] at h3
    subst h3
    have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
    have hcard := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p f)
      ⟨p, f, hp.out, hpo, hf, hK⟩
    rw [hK] at hcard
    have hcardK : Nat.card K = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv]
      exact hcard
    have h60 : 60 ∣ Nat.card K := by
      have : (2 ^ 2 * ((2 ^ 2) ^ 2 - 1)) = 60 := by norm_num
      rwa [this] at h1
    have h2' : Nat.card K ∣ d4Order 2 := h2
    have := psl2_small_check4 hp.out hf h5 hq (hcardK ▸ h60) (hcardK ▸ h2')
    rw [hcardK, this]
    norm_num
  ·
    exfalso
    have h2f := ree_factorization hcard
    rw [h2f] at h3
    subst h3
    have h39 : 3 ^ 9 ∣ Nat.card K := by
      rw [hcard, ordRee]
      refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by omega)
    have := h39.trans h2
    revert this
    norm_num [d4Order]
  ·
    exfalso
    have hc : Nat.card K = 175560 :=
      (Nat.card_congr e.toEquiv).trans
        CFSG.ComponentClassification.AschbacherTheorem3.FourEight.card_goldschmidtJ1
    rw [hc, show (175560 : ℕ) = 2 ^ 3 * 21945 by norm_num,
      factorization_two_pow_mul_odd 3 (by decide)] at h3
    subst h3
    rw [hc] at h1
    revert h1
    norm_num

theorem card_eq_of_carries3 {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Group K] [Finite K] (hK : goldschmidtSimpleType K)
    (h1 : (2 ^ n) ^ 3 * (((2 ^ n) ^ 3) ^ 2 - 1) ∣ Nat.card K)
    (h3 : (Nat.card K).factorization 2 = 3 * n) :
    Nat.card K = (2 ^ n) ^ 3 * (((2 ^ n) ^ 3) ^ 2 - 1) := by
  have hpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have h3d : 3 ∣ ((2 ^ n) ^ 3) ^ 2 - 1 := by
    have := three_dvd_two_pow_sq_sub_one (3 * n)
    rwa [pow_mul'] at this
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, h5, hq, ⟨e⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e⟩⟩
  ·
    have hcard : Nat.card K = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
      (Nat.card_congr e.toEquiv).trans (NearSolvable.card_psl2_even (by omega))
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      rw [← pow_mul]; exact odd_two_pow_sub_one (by omega)
    rw [hcard, factorization_two_pow_mul_odd f hodd] at h3
    have hf3 : 2 ^ f = (2 ^ n) ^ 3 := by rw [h3, ← pow_mul, mul_comm]
    rw [hcard, hf3]
  ·
    exact absurd ((h3d.mul_left ((2 ^ n) ^ 3)).trans h1) (sz_not_three_dvd e)
  ·
    exfalso
    have h := NearSolvable.card_psu3_mul_gcd (p := f) (by omega)
    rw [← Nat.card_congr e.toEquiv] at h
    have hg : Odd (Nat.gcd 3 (2 ^ f + 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
    have hodd : Odd (((2 ^ f) ^ 2 - 1) * (2 ^ (f * 3) + 1)) := by
      rw [← pow_mul]
      exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_add_one (by omega))
    have hfac : (Nat.card K * Nat.gcd 3 (2 ^ f + 1)).factorization 2 =
        ((2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))).factorization 2 := by
      rw [h]
    rw [Nat.factorization_mul hpos hg.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hg.not_two_dvd_nat, add_zero, ← pow_mul,
      factorization_two_pow_mul_odd _ hodd] at hfac
    rw [hfac] at h3
    have hfn : f = n := by omega
    subst hfn
    have hK1 : Nat.card K ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      rw [← h]; exact Dvd.intro _ rfl
    have h1' := h1.trans hK1
    have hq1 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq3 : 1 ≤ (2 ^ f) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h1'' := Nat.dvd_of_mul_dvd_mul_left (pow_pos (by omega : 0 < 2 ^ f) 3) h1'
    rw [sq_sub_one_eq_mul (x := (2 ^ f) ^ 3) hq3, mul_comm ((2 ^ f) ^ 3 + 1)] at h1''
    have h1''' := Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < (2 ^ f) ^ 3 + 1) h1''
    exact not_dvd_cube_sub_one hq1 h1'''
  ·
    have h2f := psl2_odd_factorization hpo hf hq e
    omega
  ·
    have h2f := ree_factorization hcard
    omega
  ·
    have hc : Nat.card K = 175560 :=
      (Nat.card_congr e.toEquiv).trans
        CFSG.ComponentClassification.AschbacherTheorem3.FourEight.card_goldschmidtJ1
    rw [hc, show (175560 : ℕ) = 2 ^ 3 * 21945 by norm_num,
      factorization_two_pow_mul_odd 3 (by decide)] at h3
    omega

theorem not_dvd_aux {x : ℕ} (hx : 16 ≤ x) : ¬ ((x ^ 3 - 1) * (x - 1) ∣ x ^ 4 - 1) := by
  intro h
  have hx1 : 0 < x - 1 := by omega
  have e : x ^ 4 - 1 = (x - 1) * (x ^ 3 + x ^ 2 + x + 1) := by
    have : x ^ 4 = (x - 1) * (x ^ 3 + x ^ 2 + x + 1) + 1 := by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega
  rw [e, mul_comm (x ^ 3 - 1)] at h
  have h' := Nat.dvd_of_mul_dvd_mul_left hx1 h
  have h1 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h'' : x ^ 3 - 1 ∣ x ^ 2 + x + 2 := by
    have e2 : x ^ 3 + x ^ 2 + x + 1 = (x ^ 3 - 1) + (x ^ 2 + x + 2) := by omega
    rw [e2] at h'
    exact (Nat.dvd_add_right (dvd_refl _)).1 h'
  have := Nat.le_of_dvd (by omega) h''
  have h16 : x ^ 3 ≥ 16 * x ^ 2 := by nlinarith [sq_nonneg x]
  have h16' : x ^ 2 ≥ 16 * x := by nlinarith
  omega

theorem big_ineq {q : ℕ} (hq : 4 ≤ q) : q ^ 7 + q ^ 3 < (q ^ 6 - 1) * (q ^ 2 - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 4 := ⟨q - 4, by omega⟩
  have h6 : 1 ≤ (r + 4) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (r + 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h6, h2]
  nlinarith [sq_nonneg (r : ℤ), pow_nonneg (show (0 : ℤ) ≤ r by positivity) 3,
    pow_nonneg (show (0 : ℤ) ≤ r by positivity) 4, pow_nonneg (show (0 : ℤ) ≤ r by positivity) 5,
    pow_nonneg (show (0 : ℤ) ≤ r by positivity) 6, pow_nonneg (show (0 : ℤ) ≤ r by positivity) 7,
    pow_nonneg (show (0 : ℤ) ≤ r by positivity) 8]

theorem false_of_carries_both2 {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Group K] [Finite K] (hK : goldschmidtSimpleType K)
    (h1 : ((2 ^ n) ^ 3 * (((2 ^ n) ^ 3) ^ 2 - 1)) * (2 ^ n * ((2 ^ n) ^ 2 - 1)) ∣ Nat.card K)
    (h3 : (Nat.card K).factorization 2 = 4 * n) : False := by
  have hpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hq4 : 4 ≤ 2 ^ n := four_le_two_pow hn
  have h3d : 3 ∣ (2 ^ n) ^ 2 - 1 := three_dvd_two_pow_sq_sub_one n
  have h3K : 3 ∣ Nat.card K :=
    (((h3d.mul_left (2 ^ n)).trans (dvd_mul_left _ _))).trans h1
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, h5, hq, ⟨e⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e⟩⟩
  ·
    have hcard : Nat.card K = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
      (Nat.card_congr e.toEquiv).trans (NearSolvable.card_psl2_even (by omega))
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      rw [← pow_mul]; exact odd_two_pow_sub_one (by omega)
    rw [hcard, factorization_two_pow_mul_odd f hodd] at h3
    rw [hcard] at h1
    have hx : 2 ^ f = (2 ^ n) ^ 4 := by rw [h3, pow_mul']
    rw [hx] at h1
    generalize hqdef : 2 ^ n = q at h1 hq4
    have hq0 : 0 < q := by omega
    have e1 : (q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1)) =
        q ^ 4 * (((q ^ 2) ^ 3 - 1) * (q ^ 2 - 1)) := by
      have : (q ^ 3) ^ 2 = (q ^ 2) ^ 3 := by ring
      rw [this]; ring
    have e2 : q ^ 4 * (((q ^ 4) ^ 2) - 1) = q ^ 4 * ((q ^ 2) ^ 4 - 1) := by
      have : (q ^ 4) ^ 2 = (q ^ 2) ^ 4 := by ring
      rw [this]
    rw [e1, e2] at h1
    have h1' := Nat.dvd_of_mul_dvd_mul_left (pow_pos hq0 4) h1
    have hx16 : 16 ≤ q ^ 2 := by nlinarith
    exact not_dvd_aux hx16 h1'
  ·
    exact absurd h3K (sz_not_three_dvd e)
  ·
    have h := NearSolvable.card_psu3_mul_gcd (p := f) (by omega)
    rw [← Nat.card_congr e.toEquiv] at h
    have hg : Odd (Nat.gcd 3 (2 ^ f + 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
    have hodd : Odd (((2 ^ f) ^ 2 - 1) * (2 ^ (f * 3) + 1)) := by
      rw [← pow_mul]
      exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_add_one (by omega))
    have hfac : (Nat.card K * Nat.gcd 3 (2 ^ f + 1)).factorization 2 =
        ((2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))).factorization 2 := by
      rw [h]
    rw [Nat.factorization_mul hpos hg.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hg.not_two_dvd_nat, add_zero, ← pow_mul,
      factorization_two_pow_mul_odd _ hodd] at hfac
    rw [hfac] at h3
    have hqq : (2 ^ f) ^ 3 = (2 ^ n) ^ 4 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    have hLK : ((2 ^ n) ^ 3 * (((2 ^ n) ^ 3) ^ 2 - 1)) * (2 ^ n * ((2 ^ n) ^ 2 - 1)) ≤
        Nat.card K := Nat.le_of_dvd Nat.card_pos h1
    have hKg : Nat.card K ≤ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      rw [← h]
      exact Nat.le_mul_of_pos_right _ hg.pos
    rw [hqq] at hKg
    generalize hq'def : 2 ^ f = q' at hKg hqq
    generalize hqdef : 2 ^ n = q at hLK hKg hqq hq4
    have hq0 : 0 < q := by omega
    have hq'2 : q' ^ 2 ≤ q ^ 3 := by
      by_contra hlt
      push Not at hlt
      have h9 : (q ^ 3) ^ 3 ≤ (q' ^ 2) ^ 3 := Nat.pow_le_pow_left hlt.le 3
      have h8 : (q' ^ 2) ^ 3 = q ^ 8 := by
        have : (q' ^ 2) ^ 3 = (q' ^ 3) ^ 2 := by ring
        rw [this, hqq]; ring
      have h99 : (q ^ 3) ^ 3 = q ^ 9 := by ring
      rw [h8, h99] at h9
      have : q ^ 8 < q ^ 9 := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have hK2 : (q' ^ 2 - 1) * (q ^ 4 + 1) ≤ q ^ 3 * (q ^ 4 + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have key := big_ineq hq4
    have e1 : (q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1)) =
        q ^ 4 * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
      have : (q ^ 3) ^ 2 = q ^ 6 := by ring
      rw [this]; ring
    have e3 : q ^ 4 * ((q' ^ 2 - 1) * (q ^ 4 + 1)) ≤ q ^ 4 * (q ^ 3 * (q ^ 4 + 1)) :=
      Nat.mul_le_mul_left _ hK2
    have e4 : q ^ 4 * (q ^ 3 * (q ^ 4 + 1)) = q ^ 4 * (q ^ 7 + q ^ 3) := by ring
    have hlt : q ^ 4 * ((q' ^ 2 - 1) * (q ^ 4 + 1)) < q ^ 4 * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
      calc q ^ 4 * ((q' ^ 2 - 1) * (q ^ 4 + 1)) ≤ q ^ 4 * (q ^ 7 + q ^ 3) := e4 ▸ e3
        _ < q ^ 4 * ((q ^ 6 - 1) * (q ^ 2 - 1)) := Nat.mul_lt_mul_of_pos_left key (pow_pos hq0 4)
    rw [e1] at hLK
    omega
  · have h2f := psl2_odd_factorization hpo hf hq e
    omega
  · have h2f := ree_factorization hcard
    omega
  · have hc : Nat.card K = 175560 :=
      (Nat.card_congr e.toEquiv).trans
        CFSG.ComponentClassification.AschbacherTheorem3.FourEight.card_goldschmidtJ1
    rw [hc, show (175560 : ℕ) = 2 ^ 3 * 21945 by norm_num,
      factorization_two_pow_mul_odd 3 (by decide)] at h3
    omega

end CFSG.RankThree.PartOne.SEITZ7
