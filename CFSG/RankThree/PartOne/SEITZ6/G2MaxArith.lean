module

public import CFSG.Monster.B.Recog.GenericGoldschmidtArithOmega
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTypes
public import CFSG.RankThree.PartOne.SEITZ3.NatArith

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride CFSG.Monster.B.Recog.GoldschmidtArith
  CFSG.Monster.B.Recog.GoldschmidtArithOmega CFSG.RankThree.PartOne.SEITZ3 Matrix
open scoped MatrixGroups

@[expose] def g2Order (n : ℕ) : ℕ := (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)

theorem three_dvd_two_pow_sq_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 n

theorem not_dvd_cube_sub_one {x : ℕ} (hx : 2 ≤ x) : ¬ (x ^ 3 - 1 ∣ x ^ 2 - 1) := by
  intro h
  have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : x ^ 2 < x ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have h4 : 0 < x ^ 2 - 1 := by
    have : 4 ≤ x ^ 2 := by nlinarith
    omega
  have := Nat.le_of_dvd h4 h
  omega

theorem psl2_small_check (m : ℕ) (h5 : 5 ≤ m) (h8 : m % 8 = 3 ∨ m % 8 = 5)
    (h60 : 60 ∣ m * (m ^ 2 - 1) / 2) (hdvd : m * (m ^ 2 - 1) / 2 ∣ g2Order 2) :
    m * (m ^ 2 - 1) / 2 = 60 := by
  have hbound : m ≤ 800 := by
    by_contra h
    push Not at h
    have hle := Nat.le_of_dvd (by norm_num [g2Order]) hdvd
    have h1 : 801 * (801 ^ 2 - 1) ≤ m * (m ^ 2 - 1) :=
      Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    have h2 := Nat.div_le_div_right (c := 2) h1
    have h3 : g2Order 2 < 801 * (801 ^ 2 - 1) / 2 := by norm_num [g2Order]
    omega
  have key : ∀ m < 801, 5 ≤ m → (m % 8 = 3 ∨ m % 8 = 5) → 60 ∣ m * (m ^ 2 - 1) / 2 →
      m * (m ^ 2 - 1) / 2 ∣ g2Order 2 → m * (m ^ 2 - 1) / 2 = 60 := by
    decide +kernel
  exact key m (by omega) h5 h8 h60 hdvd

theorem one_le_two_part {K : Type} [Group K] [Finite K]
    (hK : goldschmidtSimpleType K) : 1 ≤ (Nat.card K).factorization 2 := by
  have hpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, h5, hq, ⟨e⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e⟩⟩
  · have hcard : Nat.card K = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
      (Nat.card_congr e.toEquiv).trans (NearSolvable.card_psl2_even (by omega))
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      rw [← pow_mul]; exact odd_two_pow_sub_one (by omega)
    rw [hcard, factorization_two_pow_mul_odd f hodd]
    omega
  · rw [Nat.card_congr e.toEquiv, NearSolvable.card_sz m, mul_assoc, ← pow_mul,
      factorization_two_pow_mul_odd _
        ((odd_two_pow_add_one (by omega)).mul (odd_two_pow_sub_one (by omega)))]
    omega
  · have h := NearSolvable.card_psu3_mul_gcd (p := f) (by omega)
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
    rw [hfac]
    omega
  · rw [psl2_odd_factorization hpo hf hq e]
    omega
  · rw [ree_factorization hcard]
    omega
  · have : Nat.card K = 175560 :=
      (Nat.card_congr e.toEquiv).trans
        CFSG.ComponentClassification.AschbacherTheorem3.FourEight.card_goldschmidtJ1
    rw [this, show (175560 : ℕ) = 2 ^ 3 * 21945 by norm_num,
      factorization_two_pow_mul_odd 3 (by decide)]
    omega

theorem card_eq_of_carries {n : ℕ} (hn : 2 ≤ n) {K : Type} [Group K]
    [Finite K] (hK : goldschmidtSimpleType K)
    (h1 : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card K) (h2 : Nat.card K ∣ g2Order n)
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
    have h2' : Nat.card K ∣ g2Order 2 := h2
    have := psl2_small_check (p ^ f) h5 hq (hcardK ▸ h60) (hcardK ▸ h2')
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
    norm_num [g2Order]
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

theorem coprime_pred_succ_of_even {y : ℕ} (hy : Even y) (hy1 : 1 ≤ y) :
    Nat.Coprime (y - 1) (y + 1) := by
  have hodd : Odd (y - 1) := Nat.Even.sub_odd hy1 hy odd_one
  have h2 : Nat.Coprime (y - 1) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd.not_two_dvd_nat).symm
  have : y + 1 = 2 + (y - 1) := by omega
  rw [this]
  exact Nat.coprime_add_self_right.2 h2

theorem false_of_carries_both {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Group K] [Finite K] (hK : goldschmidtSimpleType K)
    (h1 : (2 ^ n * ((2 ^ n) ^ 2 - 1)) ^ 2 ∣ Nat.card K)
    (h3 : (Nat.card K).factorization 2 = 2 * n) : False := by
  have hpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, h5, hq, ⟨e⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e⟩⟩
  ·
    have hcard : Nat.card K = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
      (Nat.card_congr e.toEquiv).trans (NearSolvable.card_psl2_even (by omega))
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      rw [← pow_mul]; exact odd_two_pow_sub_one (by omega)
    rw [hcard, factorization_two_pow_mul_odd f hodd] at h3
    rw [hcard] at h1
    have hx : 2 ^ f = (2 ^ n) ^ 2 := by rw [h3, ← pow_mul, mul_comm]
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨x, hxdef⟩ : ∃ x, x = (2 ^ n) ^ 2 := ⟨_, rfl⟩
    have hx16 : 16 ≤ x := by rw [hxdef]; nlinarith
    have hsq : (2 ^ n * ((2 ^ n) ^ 2 - 1)) ^ 2 = x * (x - 1) ^ 2 := by
      rw [mul_pow, ← hxdef]
    rw [hsq, hx, ← hxdef] at h1
    have h1' := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < x) h1
    rw [sq_sub_one_eq_mul (x := x) (by omega), pow_two] at h1'
    have h1'' := Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < x - 1) h1'
    have h2 : x - 1 ∣ 2 := by
      have : x + 1 = (x - 1) + 2 := by omega
      rw [this] at h1''
      exact (Nat.dvd_add_right (dvd_refl _)).1 h1''
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  ·
    exact absurd ((((three_dvd_two_pow_sq_sub_one n).mul_left (2 ^ n)).trans
      (dvd_pow_self _ (by norm_num))).trans h1) (sz_not_three_dvd e)
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
    have hqq : (2 ^ n) ^ 2 = (2 ^ f) ^ 3 := by
      rw [← pow_mul, ← pow_mul, mul_comm n 2, ← h3]
    have hK1 : Nat.card K ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      rw [← h]; exact Dvd.intro _ rfl
    have h1' := h1.trans hK1
    rw [mul_pow, hqq] at h1'
    have hq1 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1'' := Nat.dvd_of_mul_dvd_mul_left (pow_pos (by omega : 0 < 2 ^ f) 3) h1'
    have hev : Even ((2 ^ f) ^ 3) :=
      Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩
    have hcop : Nat.Coprime (((2 ^ f) ^ 3 - 1) ^ 2) ((2 ^ f) ^ 3 + 1) :=
      (coprime_pred_succ_of_even hev (Nat.one_le_pow _ _ (by omega))).pow_left 2
    rw [mul_comm] at h1''
    have h2 := hcop.dvd_of_dvd_mul_left h1''
    exact not_dvd_cube_sub_one hq1 ((dvd_pow_self _ (by norm_num)).trans h2)
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

end CFSG.RankThree.PartOne.SEITZ6
