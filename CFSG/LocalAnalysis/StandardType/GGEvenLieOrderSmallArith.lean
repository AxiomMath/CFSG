module

public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsBasic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private lemma ggoOddTwoPowSubOne {f : ℕ} (hf : 0 < f) : Odd (2 ^ f - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow
    (even_iff_two_dvd.mpr (dvd_pow_self 2 hf.ne')) odd_one

private lemma ggoOddTwoPowAddOne {f : ℕ} (hf : 0 < f) : Odd (2 ^ f + 1) :=
  Even.add_odd (even_iff_two_dvd.mpr (dvd_pow_self 2 hf.ne')) odd_one

private lemma ggoGcdTwoOdd {n : ℕ} (hn : Odd n) : Nat.gcd 2 n = 1 :=
  (Nat.coprime_two_left.mpr hn).gcd_eq_one

private lemma ggoDvdMulDivOfDvd {a P d : ℕ} (h : d ∣ P) : a ∣ a * P / d := by
  rw [Nat.mul_div_assoc a h]
  exact dvd_mul_right a _

private lemma ggoSubOneDvdSqSubOne (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2

private lemma ggoAddOneDvdSqSubOne (q : ℕ) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · zify [Nat.one_le_pow 2 q hq, hq]
      ring⟩

private lemma ggoToNatTwo {q : ℕ} (hq : 1 ≤ q) :
    (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := by
  have h2 : (1 : ℕ) ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
  have hcast : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub h2]
    push_cast
    ring
  rw [hcast, Int.toNat_natCast]

private lemma ggoIntFactorNonneg (q i : ℕ) (hq : 1 ≤ q) :
    0 ≤ (q : ℤ) ^ i - (-1 : ℤ) ^ i := by
  have h1 : (1 : ℤ) ≤ (q : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast hq)
  have h2 : (-1 : ℤ) ^ i ≤ 1 := by
    rcases Nat.even_or_odd i with hi | hi
    · rw [hi.neg_one_pow]
    · rw [hi.neg_one_pow]; norm_num
  linarith

private theorem ggoNotExcThreeOrderOfTwoPowDvd {ord a N : ℕ} (hN : 12 < a * N)
    (hdvd : 2 ^ (a * N) ∣ ord) : GGNotExcThreeOrder ord := by
  have hb := ggAKFG_le_of_dvd (z := 1) odd_one (by simpa using hdvd)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := hb.1 h; omega
  · have := hb.2.1 h; omega
  · have := hb.2.2 h; omega

private theorem ggoNotExcThreeOrderOrdA {d a : ℕ} (hd : 2 ≤ d) (ha : 1 ≤ a) :
    GGNotExcThreeOrder (CFSG.Open.ordA (d - 1) (2 ^ a)) := by
  have h1 : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  simpa only [CFSG.Open.ordA, h1, Nat.mul_comm (d - 1) d] using
    ggAKFG_ordSL_good (d := d) (a := a) hd ha

private theorem ggoNotExcThreeOrderOrdBC {s a : ℕ} (hs : 1 ≤ s) (ha : 2 ≤ a) :
    GGNotExcThreeOrder (CFSG.Open.ordBC s (2 ^ a)) := by
  have hgcd : Nat.gcd 2 (2 ^ a - 1) = 1 :=
    ggoGcdTwoOdd (ggoOddTwoPowSubOne (by omega))
  have heq : CFSG.Open.ordBC s (2 ^ a) =
      (2 ^ a) ^ (s ^ 2) * ∏ j ∈ Finset.Icc 1 s, ((2 ^ a) ^ (2 * j) - 1) := by
    unfold CFSG.Open.ordBC
    rw [hgcd, Nat.div_one]
    simp only [pow_two]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact ggAKFG_ordSp_ne (a := a) (s := s) (N₀ := 174182400) (z := 1) ha hs (Or.inl rfl)
      odd_one (by rw [← heq]; simpa using h)
  · exact ggAKFG_ordSp_ne (a := a) (s := s) (N₀ := 25920) (z := 1) ha hs
      (Or.inr (Or.inl rfl)) odd_one (by rw [← heq]; simpa using h)
  · exact ggAKFG_ordSp_ne (a := a) (s := s) (N₀ := 360) (z := 1) ha hs
      (Or.inr (Or.inr rfl)) odd_one (by rw [← heq]; simpa using h)

private theorem ggoNotExcThreeOrderOrdTwistedA {d a : ℕ} (hd : 2 ≤ d) (ha : 2 ≤ a) :
    GGNotExcThreeOrder (CFSG.Open.ordTwistedA (d - 1) (2 ^ a)) := by
  have h1 : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  have hq1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hoddq : Odd (2 ^ a + 1) := ggoOddTwoPowAddOne (by omega)
  have hgodd : Odd (Nat.gcd d (2 ^ a + 1)) :=
    Odd.of_dvd_nat hoddq (Nat.gcd_dvd_right _ _)
  have hdivP : Nat.gcd d (2 ^ a + 1) ∣
      ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    refine (ggoAddOneDvdSqSubOne (2 ^ a)).trans ?_
    rw [← ggoToNatTwo hq1]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, hd⟩)
  have hmain : (2 ^ a) ^ ((d - 1) * d / 2) *
        ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat =
      CFSG.Open.ordTwistedA (d - 1) (2 ^ a) * Nat.gcd d (2 ^ a + 1) := by
    unfold CFSG.Open.ordTwistedA
    rw [h1]
    rw [Nat.div_mul_cancel (dvd_mul_of_dvd_right hdivP _)]
  have hcast : ((((2 ^ a) ^ ((d - 1) * d / 2)) *
        ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat : ℕ) : ℤ) =
      ((2 ^ a : ℕ) : ℤ) ^ (d * (d - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i) := by
    rw [Nat.cast_mul, Nat.cast_prod]
    congr 1
    · rw [Nat.cast_pow, Nat.mul_comm (d - 1) d]
    · exact Finset.prod_congr rfl fun i _ =>
        Int.toNat_of_nonneg (ggoIntFactorNonneg (2 ^ a) i hq1)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact ggAKFG_ordSU_ne (a := a) (d := d) (N₀ := 174182400)
      (z := Nat.gcd d (2 ^ a + 1)) ha hd (Or.inl rfl) hgodd
      (by rw [← hcast, hmain, h])
  · exact ggAKFG_ordSU_ne (a := a) (d := d) (N₀ := 25920)
      (z := Nat.gcd d (2 ^ a + 1)) ha hd (Or.inr (Or.inl rfl)) hgodd
      (by rw [← hcast, hmain, h])
  · exact ggAKFG_ordSU_ne (a := a) (d := d) (N₀ := 360)
      (z := Nat.gcd d (2 ^ a + 1)) ha hd (Or.inr (Or.inr rfl)) hgodd
      (by rw [← hcast, hmain, h])

private lemma ggoPowDvdOrdD (k q : ℕ) : q ^ (k * (k - 1)) ∣ CFSG.Open.ordD k q := by
  unfold CFSG.Open.ordD
  rw [mul_assoc (q ^ (k * (k - 1)))]
  exact ggoDvdMulDivOfDvd ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _))

private lemma ggoPowDvdOrdTwistedD (k q : ℕ) :
    q ^ (k * (k - 1)) ∣ CFSG.Open.ordTwistedD k q := by
  unfold CFSG.Open.ordTwistedD
  rw [mul_assoc (q ^ (k * (k - 1)))]
  exact ggoDvdMulDivOfDvd ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _))

private lemma ggoPowDvdOrdE6 (q : ℕ) : q ^ 36 ∣ CFSG.Open.ordE6 q := by
  unfold CFSG.Open.ordE6
  simp only [mul_assoc]
  refine ggoDvdMulDivOfDvd ((Nat.gcd_dvd_right _ _).trans ?_)
  exact (((((ggoSubOneDvdSqSubOne q).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _

private lemma ggoPowDvdOrdTwistedE6 (q : ℕ) : q ^ 36 ∣ CFSG.Open.ordTwistedE6 q := by
  unfold CFSG.Open.ordTwistedE6
  simp only [mul_assoc]
  refine ggoDvdMulDivOfDvd ((Nat.gcd_dvd_right _ _).trans ?_)
  exact (((((ggoAddOneDvdSqSubOne q).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _

private lemma ggoPowDvdOrdE7 (q : ℕ) : q ^ 63 ∣ CFSG.Open.ordE7 q := by
  unfold CFSG.Open.ordE7
  simp only [mul_assoc]
  refine ggoDvdMulDivOfDvd ((Nat.gcd_dvd_right _ _).trans ?_)
  exact ((((((ggoSubOneDvdSqSubOne q).mul_left _).mul_left _).mul_left _).mul_left _).mul_left
    _).mul_left _

private lemma ggoTwoPowDvdOrdD (k f : ℕ) :
    2 ^ (f * (k * (k - 1))) ∣ CFSG.Open.ordD k (2 ^ f) := by
  simpa only [pow_mul] using ggoPowDvdOrdD k (2 ^ f)

private lemma ggoTwoPowDvdOrdTwistedD (k f : ℕ) :
    2 ^ (f * (k * (k - 1))) ∣ CFSG.Open.ordTwistedD k (2 ^ f) := by
  simpa only [pow_mul] using ggoPowDvdOrdTwistedD k (2 ^ f)

private lemma ggoTwoPowDvdOrdE6 (f : ℕ) : 2 ^ (f * 36) ∣ CFSG.Open.ordE6 (2 ^ f) := by
  simpa only [pow_mul] using ggoPowDvdOrdE6 (2 ^ f)

private lemma ggoTwoPowDvdOrdTwistedE6 (f : ℕ) :
    2 ^ (f * 36) ∣ CFSG.Open.ordTwistedE6 (2 ^ f) := by
  simpa only [pow_mul] using ggoPowDvdOrdTwistedE6 (2 ^ f)

private lemma ggoTwoPowDvdOrdE7 (f : ℕ) : 2 ^ (f * 63) ∣ CFSG.Open.ordE7 (2 ^ f) := by
  simpa only [pow_mul] using ggoPowDvdOrdE7 (2 ^ f)

private lemma ggoTwoPowDvdOrdE8 (f : ℕ) : 2 ^ (f * 120) ∣ CFSG.Open.ordE8 (2 ^ f) := by
  unfold CFSG.Open.ordE8
  rw [pow_mul]
  simp only [mul_assoc]
  exact dvd_mul_right _ _

private lemma ggoTwoPowDvdOrdF4 (f : ℕ) : 2 ^ (f * 24) ∣ CFSG.Open.ordF4 (2 ^ f) := by
  unfold CFSG.Open.ordF4
  rw [pow_mul]
  simp only [mul_assoc]
  exact dvd_mul_right _ _

private lemma ggoTwoPowDvdOrdTrialityD4 (f : ℕ) :
    2 ^ (f * 12) ∣ CFSG.Open.ordTrialityD4 (2 ^ f) := by
  unfold CFSG.Open.ordTrialityD4
  rw [pow_mul]
  simp only [mul_assoc]
  exact dvd_mul_right _ _

private theorem ggoNotExcThreeOrderOrdG2 {a : ℕ} (ha : 2 ≤ a) (ha3 : a ≤ 3) :
    GGNotExcThreeOrder (CFSG.Open.ordG2 (2 ^ a)) := by
  interval_cases a <;> norm_num [CFSG.Open.ordG2, GGNotExcThreeOrder]

theorem evenLieOrder_notExcThree_of_label {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hc : markChar lab = 2) (hd : 2 ≤ markDeg lab) (hd3 : markDeg lab ≤ 3)
    (h1 : lab.tag ≠ .twB2) (h2 : lab.tag ≠ .twF4) (h3 : lab.tag ≠ .twF4der) :
    GGNotExcThreeOrder
      (CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag lab) (markRank lab) (markDeg lab)) := by
  obtain ⟨t, r, n⟩ := lab
  cases t
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      LargeEvenInLambda2] at hd hd3 hlab ⊢
    obtain ⟨hn, hr, -⟩ := hlab
    exact ggoNotExcThreeOrderOrdA (d := r + 1) (a := n) (by omega) hn
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      LargeEvenInLambda2] at hd hd3 hlab ⊢
    obtain ⟨hn, hr, -⟩ := hlab
    exact ggoNotExcThreeOrderOrdTwistedA (d := r + 1) (a := n) (by omega) hd
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      LargeEvenInLambda2] at hd hd3 hlab ⊢
    obtain ⟨hn, hr, -⟩ := hlab
    exact ggoNotExcThreeOrderOrdBC (s := r) (a := n) (by omega) hd
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      LargeEvenInLambda2] at hd hd3 hlab ⊢
    obtain ⟨hn, hr, -⟩ := hlab
    exact ggoNotExcThreeOrderOrdBC (s := r) (a := n) (by omega) hd
  ·
    by_cases hr : r = 3
    · simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
        if_pos hr, LargeEvenInLambda2] at hd hd3 hlab ⊢
      exact ggoNotExcThreeOrderOrdA (d := 4) (a := n) (by norm_num) (by omega)
    · simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
        if_neg hr, LargeEvenInLambda2] at hd hd3 hlab ⊢
      obtain ⟨hn, hr3⟩ := hlab
      have hr4 : 4 ≤ r := by omega
      have hN : 12 < n * (r * (r - 1)) := by
        have hr1 : 3 ≤ r - 1 := by omega
        have h24 : 2 * (4 * 3) ≤ n * (r * (r - 1)) := Nat.mul_le_mul hd (Nat.mul_le_mul hr4 hr1)
        omega
      exact ggoNotExcThreeOrderOfTwoPowDvd (ord := CFSG.Open.ordD r (2 ^ n)) (a := n)
        (N := r * (r - 1)) hN (ggoTwoPowDvdOrdD r n)
  ·
    by_cases hr2 : r = 2
    · simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
        if_pos hr2, LargeEvenInLambda2] at hd hd3 hlab ⊢
      exact ggoNotExcThreeOrderOrdA (d := 2) (a := 2 * n) (by norm_num) (by omega)
    · by_cases hr3 : r = 3
      · simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
          if_neg hr2, if_pos hr3, LargeEvenInLambda2] at hd hd3 hlab ⊢
        exact ggoNotExcThreeOrderOrdTwistedA (d := 4) (a := n) (by norm_num) hd
      · simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
          if_neg hr2, if_neg hr3, LargeEvenInLambda2] at hd hd3 hlab ⊢
        obtain ⟨hn, hr2'⟩ := hlab
        have hr4 : 4 ≤ r := by omega
        have hN : 12 < n * (r * (r - 1)) := by
          have hr1 : 3 ≤ r - 1 := by omega
          have h24 : 2 * (4 * 3) ≤ n * (r * (r - 1)) :=
            Nat.mul_le_mul hd (Nat.mul_le_mul hr4 hr1)
          omega
        exact ggoNotExcThreeOrderOfTwoPowDvd (ord := CFSG.Open.ordTwistedD r (2 ^ n)) (a := n)
          (N := r * (r - 1)) hN (ggoTwoPowDvdOrdTwistedD r n)
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hd hd3 ⊢
    exact ggoNotExcThreeOrderOfTwoPowDvd (ord := CFSG.Open.ordE6 (2 ^ n)) (a := n) (N := 36)
      (by omega) (ggoTwoPowDvdOrdE6 n)
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hd hd3 ⊢
    exact ggoNotExcThreeOrderOfTwoPowDvd (ord := CFSG.Open.ordE7 (2 ^ n)) (a := n) (N := 63)
      (by omega) (ggoTwoPowDvdOrdE7 n)
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hd hd3 ⊢
    exact ggoNotExcThreeOrderOfTwoPowDvd (ord := CFSG.Open.ordE8 (2 ^ n)) (a := n) (N := 120)
      (by omega) (ggoTwoPowDvdOrdE8 n)
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hd hd3 ⊢
    exact ggoNotExcThreeOrderOfTwoPowDvd (ord := CFSG.Open.ordF4 (2 ^ n)) (a := n) (N := 24)
      (by omega) (ggoTwoPowDvdOrdF4 n)
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hd hd3 ⊢
    exact ggoNotExcThreeOrderOfTwoPowDvd (ord := CFSG.Open.ordTwistedE6 (2 ^ n)) (a := n)
      (N := 36) (by omega) (ggoTwoPowDvdOrdTwistedE6 n)
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hd hd3 ⊢
    exact ggoNotExcThreeOrderOfTwoPowDvd (ord := CFSG.Open.ordTrialityD4 (2 ^ n)) (a := n)
      (N := 12) (by omega) (ggoTwoPowDvdOrdTrialityD4 n)
  ·
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hd hd3 ⊢
    exact ggoNotExcThreeOrderOrdG2 hd hd3
  ·
    exact absurd rfl h1
  ·
    exact absurd rfl h2
  ·
    exact absurd hc (by simp [markChar])
  ·
    exact absurd hc (by simp [markChar])
  ·
    exact absurd rfl h3

end CFSG.StandardType
