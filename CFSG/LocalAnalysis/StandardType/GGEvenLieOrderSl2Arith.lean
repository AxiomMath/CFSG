module

public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
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
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open

private theorem toNat_sq_sub_neg_one_sq (q : ℕ) :
    ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq
    rw [show ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [h1]; ring]
    exact Int.toNat_natCast _

private theorem toNat_pow_sub_neg_one_pow_of_odd {q k : ℕ} (hk : Odd k) :
    ((q : ℤ) ^ k - (-1 : ℤ) ^ k).toNat = q ^ k + 1 := by
  rw [hk.neg_one_pow, sub_neg_eq_add]
  rw [show (q : ℤ) ^ k + 1 = ((q ^ k + 1 : ℕ) : ℤ) by push_cast; ring]
  exact Int.toNat_natCast _

private theorem gcd_two_eq_one_of_even {q : ℕ} (hq : Even q) (h1 : 1 ≤ q) :
    Nat.gcd 2 (q - 1) = 1 :=
  Nat.coprime_two_left.mpr (Nat.Even.sub_odd h1 hq odd_one)

private theorem gcd_four_eq_one_of_odd {n : ℕ} (hn : Odd n) : Nat.gcd 4 n = 1 := by
  have h : Nat.Coprime (2 ^ 2 : ℕ) n :=
    (Nat.coprime_pow_left_iff (n := 2) (by norm_num) 2 n).mpr (Nat.coprime_two_left.mpr hn)
  simpa using h

private theorem odd_pow_sub_one {q k : ℕ} (hq : Even q) (hk : k ≠ 0) (h1 : 1 ≤ q) :
    Odd (q ^ k - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow k q h1) (hq.pow_of_ne_zero hk) odd_one

private theorem odd_pow_add_one {q k : ℕ} (hq : Even q) (hk : k ≠ 0) :
    Odd (q ^ k + 1) :=
  (hq.pow_of_ne_zero hk).add_odd odd_one

private theorem sub_one_dvd_pow_sub_one (q k : ℕ) : q - 1 ∣ q ^ k - 1 :=
  Nat.sub_one_dvd_pow_sub_one q k

private theorem sl2_dvd_pow_mul_div {q e g P : ℕ} (he : e ≠ 0) (hg : g ∣ P)
    (hA : q ^ 2 - 1 ∣ P / g) : q * (q ^ 2 - 1) ∣ q ^ e * P / g := by
  rw [Nat.mul_div_assoc _ hg]
  exact Nat.mul_dvd_mul (dvd_pow_self q he) hA

private theorem sl2_dvd_pow_mul {q e P : ℕ} (he : e ≠ 0) (hA : q ^ 2 - 1 ∣ P) :
    q * (q ^ 2 - 1) ∣ q ^ e * P :=
  Nat.mul_dvd_mul (dvd_pow_self q he) hA

private theorem expA_ne_zero {k : ℕ} (hk : 2 ≤ k) : k * (k + 1) / 2 ≠ 0 := by
  have h6 : 6 ≤ k * (k + 1) := by
    have h := Nat.mul_le_mul hk (show 3 ≤ k + 1 by omega)
    simpa using h
  exact (Nat.div_pos (by omega : 2 ≤ k * (k + 1)) (by norm_num)).ne'

private theorem expBC_ne_zero {k : ℕ} (hk : 1 ≤ k) : k * k ≠ 0 :=
  Nat.mul_ne_zero (by omega) (by omega)

private theorem expD_ne_zero {k : ℕ} (hk : 2 ≤ k) : k * (k - 1) ≠ 0 :=
  Nat.mul_ne_zero (by omega) (by omega)

private theorem sl2_dvd_ordA {k q : ℕ} (hk : 1 ≤ k) (hq : Even q) (hq2 : 2 ≤ q) :
    q * (q ^ 2 - 1) ∣ ordA k q := by
  by_cases hk1 : k = 1
  · subst hk1
    unfold ordA
    have hg : Nat.gcd (1 + 1) (q - 1) = 1 := by
      simpa using gcd_two_eq_one_of_even hq (by omega)
    have hprod : (∏ i ∈ Finset.Icc 2 (1 + 1), (q ^ i - 1)) = q ^ 2 - 1 := by
      rw [show (1 : ℕ) + 1 = 2 from rfl, Finset.Icc_self, Finset.prod_singleton]
    have he1 : 1 * (1 + 1) / 2 = 1 := by norm_num
    simpa [hprod, he1, hg] using dvd_refl (q * (q ^ 2 - 1))
  · have hk2 : 2 ≤ k := by omega
    set P : ℕ := ∏ i ∈ Finset.Icc 2 (k + 1), (q ^ i - 1) with hPdef
    set P' : ℕ := ∏ i ∈ (Finset.Icc 2 (k + 1)).erase 2, (q ^ i - 1) with hP'def
    have h2mem : 2 ∈ Finset.Icc 2 (k + 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have h3mem : 3 ∈ (Finset.Icc 2 (k + 1)).erase 2 :=
      Finset.mem_erase.mpr ⟨by norm_num, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    have hsplit : P = (q ^ 2 - 1) * P' := by
      rw [hPdef, hP'def, ← Finset.mul_prod_erase _ _ h2mem]
    have hg' : Nat.gcd (k + 1) (q - 1) ∣ P' :=
      (Nat.gcd_dvd_right _ _).trans
        ((sub_one_dvd_pow_sub_one q 3).trans (Finset.dvd_prod_of_mem _ h3mem))
    have hg : Nat.gcd (k + 1) (q - 1) ∣ P := by
      rw [hsplit]; exact dvd_mul_of_dvd_right hg' _
    have hA : q ^ 2 - 1 ∣ P / Nat.gcd (k + 1) (q - 1) := by
      rw [hsplit, Nat.mul_div_assoc _ hg']
      exact dvd_mul_right _ _
    unfold ordA
    rw [← hPdef]
    exact sl2_dvd_pow_mul_div (expA_ne_zero hk2) hg hA

private theorem sl2_dvd_ordTwistedA {k q : ℕ} (hk : 2 ≤ k) (hq2 : 2 ≤ q) :
    q * (q ^ 2 - 1) ∣ ordTwistedA k q := by
  set P : ℕ := ∏ i ∈ Finset.Icc 2 (k + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat with hPdef
  set P' : ℕ := ∏ i ∈ (Finset.Icc 2 (k + 1)).erase 2,
      ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat with hP'def
  have h2mem : 2 ∈ Finset.Icc 2 (k + 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have h3mem : 3 ∈ (Finset.Icc 2 (k + 1)).erase 2 :=
    Finset.mem_erase.mpr ⟨by norm_num, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hsplit : P = (q ^ 2 - 1) * P' := by
    rw [hPdef, hP'def, ← Finset.mul_prod_erase _ _ h2mem, toNat_sq_sub_neg_one_sq]
  have hf3 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 :=
    toNat_pow_sub_neg_one_pow_of_odd (by decide : Odd 3)
  have h31 : q + 1 ∣ q ^ 3 + 1 := by
    simpa using (show Odd 3 by decide).nat_add_dvd_pow_add_pow q 1
  have hg' : Nat.gcd (k + 1) (q + 1) ∣ P' := by
    refine (Nat.gcd_dvd_right _ _).trans (h31.trans ?_)
    rw [← hf3]
    exact Finset.dvd_prod_of_mem _ h3mem
  have hg : Nat.gcd (k + 1) (q + 1) ∣ P := by
    rw [hsplit]; exact dvd_mul_of_dvd_right hg' _
  have hA : q ^ 2 - 1 ∣ P / Nat.gcd (k + 1) (q + 1) := by
    rw [hsplit, Nat.mul_div_assoc _ hg']
    exact dvd_mul_right _ _
  unfold ordTwistedA
  rw [← hPdef]
  exact sl2_dvd_pow_mul_div (expA_ne_zero hk) hg hA

private theorem sl2_dvd_ordBC {k q : ℕ} (hk : 1 ≤ k) (hq : Even q) (hq2 : 2 ≤ q) :
    q * (q ^ 2 - 1) ∣ ordBC k q := by
  have hg : Nat.gcd 2 (q - 1) = 1 := gcd_two_eq_one_of_even hq (by omega)
  have h1mem : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
  unfold ordBC
  rw [hg, Nat.div_one]
  refine sl2_dvd_pow_mul (expBC_ne_zero hk) ?_
  simpa using Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1mem

private theorem sl2_dvd_ordD {k q : ℕ} (hk : 2 ≤ k) (hq : Even q) (hq2 : 2 ≤ q) :
    q * (q ^ 2 - 1) ∣ ordD k q := by
  have hg : Nat.gcd 4 (q ^ k - 1) = 1 :=
    gcd_four_eq_one_of_odd (odd_pow_sub_one hq (by omega) (by omega))
  have h1mem : 1 ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  unfold ordD
  rw [mul_assoc, hg, Nat.div_one]
  refine sl2_dvd_pow_mul (expD_ne_zero hk) ?_
  simpa using dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1mem) (q ^ k - 1)

private theorem sl2_dvd_ordTwistedD {k q : ℕ} (hk : 2 ≤ k) (hq : Even q) (hq2 : 2 ≤ q) :
    q * (q ^ 2 - 1) ∣ ordTwistedD k q := by
  have hg : Nat.gcd 4 (q ^ k + 1) = 1 :=
    gcd_four_eq_one_of_odd (odd_pow_add_one hq (by omega))
  have h1mem : 1 ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  unfold ordTwistedD
  rw [mul_assoc, hg, Nat.div_one]
  refine sl2_dvd_pow_mul (expD_ne_zero hk) ?_
  simpa using dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1mem) (q ^ k + 1)

private theorem sl2_dvd_ordE6 (q : ℕ) : q * (q ^ 2 - 1) ∣ ordE6 q := by
  set P : ℕ := (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1)
      * (q ^ 2 - 1) with hPdef
  set P' : ℕ := (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) with hP'def
  have hsplit : P = (q ^ 2 - 1) * P' := by
    rw [hPdef, hP'def]; ac_rfl
  have hg' : Nat.gcd 3 (q - 1) ∣ P' := by
    refine (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_pow_sub_one q 5).trans ?_)
    rw [hP'def]
    exact dvd_mul_of_dvd_right dvd_rfl _
  have hg : Nat.gcd 3 (q - 1) ∣ P := by
    rw [hsplit]; exact dvd_mul_of_dvd_right hg' _
  have hA : q ^ 2 - 1 ∣ P / Nat.gcd 3 (q - 1) := by
    rw [hsplit, Nat.mul_div_assoc _ hg']
    exact dvd_mul_right _ _
  unfold ordE6
  rw [show q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1)
        * (q ^ 2 - 1) = q ^ 36 * P by rw [hPdef, hP'def]; ac_rfl]
  exact sl2_dvd_pow_mul_div (by norm_num) hg hA

private theorem sl2_dvd_ordTwistedE6 (q : ℕ) : q * (q ^ 2 - 1) ∣ ordTwistedE6 q := by
  set P : ℕ := (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1)
      * (q ^ 2 - 1) with hPdef
  set P' : ℕ := (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) with hP'def
  have hsplit : P = (q ^ 2 - 1) * P' := by
    rw [hPdef, hP'def]; ac_rfl
  have h51 : q + 1 ∣ q ^ 5 + 1 := by
    simpa using (show Odd 5 by decide).nat_add_dvd_pow_add_pow q 1
  have hg' : Nat.gcd 3 (q + 1) ∣ P' := by
    refine (Nat.gcd_dvd_right _ _).trans (h51.trans ?_)
    rw [hP'def]
    exact dvd_mul_of_dvd_right dvd_rfl _
  have hg : Nat.gcd 3 (q + 1) ∣ P := by
    rw [hsplit]; exact dvd_mul_of_dvd_right hg' _
  have hA : q ^ 2 - 1 ∣ P / Nat.gcd 3 (q + 1) := by
    rw [hsplit, Nat.mul_div_assoc _ hg']
    exact dvd_mul_right _ _
  unfold ordTwistedE6
  rw [show q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1)
        * (q ^ 2 - 1) = q ^ 36 * P by rw [hPdef, hP'def]; ac_rfl]
  exact sl2_dvd_pow_mul_div (by norm_num) hg hA

private theorem sl2_dvd_ordE7 {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    q * (q ^ 2 - 1) ∣ ordE7 q := by
  have hg : Nat.gcd 2 (q - 1) = 1 := gcd_two_eq_one_of_even hq (by omega)
  unfold ordE7
  rw [hg, Nat.div_one]
  rw [show q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1)
        * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      = q ^ 63 * (((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1)
          * (q ^ 8 - 1) * (q ^ 6 - 1)) * (q ^ 2 - 1)) by ac_rfl]
  exact sl2_dvd_pow_mul (by norm_num) (dvd_mul_of_dvd_right dvd_rfl _)

private theorem sl2_dvd_ordE8 (q : ℕ) : q * (q ^ 2 - 1) ∣ ordE8 q := by
  unfold ordE8
  rw [show q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1)
        * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
      = q ^ 120 * (((q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1)
          * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1)) * (q ^ 2 - 1)) by ac_rfl]
  exact sl2_dvd_pow_mul (by norm_num) (dvd_mul_of_dvd_right dvd_rfl _)

private theorem sl2_dvd_ordF4 (q : ℕ) : q * (q ^ 2 - 1) ∣ ordF4 q := by
  unfold ordF4
  rw [show q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      = q ^ 24 * (((q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1)) * (q ^ 2 - 1)) by ac_rfl]
  exact sl2_dvd_pow_mul (by norm_num) (dvd_mul_of_dvd_right dvd_rfl _)

private theorem sl2_dvd_ordG2 (q : ℕ) : q * (q ^ 2 - 1) ∣ ordG2 q := by
  unfold ordG2
  rw [show q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)
      = q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) by ac_rfl]
  exact sl2_dvd_pow_mul (by norm_num) (dvd_mul_of_dvd_right dvd_rfl _)

private theorem sl2_dvd_ordTrialityD4 (q : ℕ) : q * (q ^ 2 - 1) ∣ ordTrialityD4 q := by
  unfold ordTrialityD4
  rw [show q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      = q ^ 12 * (((q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1)) * (q ^ 2 - 1)) by ac_rfl]
  exact sl2_dvd_pow_mul (by norm_num) (dvd_mul_of_dvd_right dvd_rfl _)

theorem evenLieOrder_sl2_dvd_of_label {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hc : markChar lab = 2) (h1 : lab.tag ≠ .twB2) (h2 : lab.tag ≠ .twF4)
    (h3 : lab.tag ≠ .twF4der) :
    2 ^ markDeg lab * ((2 ^ markDeg lab) ^ 2 - 1) ∣
      CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag lab) (markRank lab) (markDeg lab) := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨hn, hlab⟩ := hlab
  simp only [LargeEvenLabel.n, LargeEvenLabel.rank, LargeEvenLabel.tag] at hn hlab hc h1 h2 h3
  have hEvenN : Even (2 ^ n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have h2N : 2 ≤ 2 ^ n := by
    have h := one_lt_pow' (show (1 : ℕ) < 2 by norm_num) (by omega : n ≠ 0)
    omega
  have hEven2N : Even (2 ^ (2 * n)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have h22N : 2 ≤ 2 ^ (2 * n) := by
    have h := one_lt_pow' (show (1 : ℕ) < 2 by norm_num) (by omega : 2 * n ≠ 0)
    omega
  cases t
  case A =>
    obtain ⟨hr, -⟩ := hlab
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel]
      using sl2_dvd_ordA (k := r) (q := 2 ^ n) hr hEvenN h2N
  case twA =>
    obtain ⟨hr, -⟩ := hlab
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      Nat.add_sub_cancel]
      using sl2_dvd_ordTwistedA (k := r) (q := 2 ^ n) hr h2N
  case B =>
    obtain ⟨hr, -⟩ := hlab
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
      using sl2_dvd_ordBC (k := r) (q := 2 ^ n) (by omega) hEvenN h2N
  case C =>
    obtain ⟨hr, -⟩ := hlab
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
      using sl2_dvd_ordBC (k := r) (q := 2 ^ n) (by omega) hEvenN h2N
  case D =>
    have hr : 3 ≤ r := hlab
    rcases eq_or_ne r 3 with hr3 | hr3
    · subst r
      simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
        using sl2_dvd_ordA (k := 3) (q := 2 ^ n) (by norm_num) hEvenN h2N
    · have hr4 : 4 ≤ r := by omega
      simpa [markTag, markRank, markDeg, hr3, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
        using sl2_dvd_ordD (k := r) (q := 2 ^ n) (by omega) hEvenN h2N
  case twD =>
    have hr : 2 ≤ r := hlab
    rcases eq_or_ne r 2 with hr2 | hr2
    · subst r
      simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
        using sl2_dvd_ordA (k := 1) (q := 2 ^ (2 * n)) (by norm_num) hEven2N h22N
    · rcases eq_or_ne r 3 with hr3 | hr3
      · subst r
        simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
          using sl2_dvd_ordTwistedA (k := 3) (q := 2 ^ n) (by norm_num) h2N
      · have hr4 : 4 ≤ r := by omega
        simpa [markTag, markRank, markDeg, hr2, hr3, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
          using sl2_dvd_ordTwistedD (k := r) (q := 2 ^ n) (by omega) hEvenN h2N
  case E6 =>
    have hr : r = 0 := hlab
    subst r
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
      using sl2_dvd_ordE6 (2 ^ n)
  case E7 =>
    have hr : r = 0 := hlab
    subst r
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
      using sl2_dvd_ordE7 hEvenN h2N
  case E8 =>
    have hr : r = 0 := hlab
    subst r
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
      using sl2_dvd_ordE8 (2 ^ n)
  case F4 =>
    have hr : r = 0 := hlab
    subst r
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
      using sl2_dvd_ordF4 (2 ^ n)
  case twE6 =>
    have hr : r = 0 := hlab
    subst r
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
      using sl2_dvd_ordTwistedE6 (2 ^ n)
  case triD4 =>
    have hr : r = 0 := hlab
    subst r
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
      using sl2_dvd_ordTrialityD4 (2 ^ n)
  case G2 =>
    obtain ⟨hr, -⟩ := hlab
    subst r
    simpa [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
      using sl2_dvd_ordG2 (2 ^ n)
  case twB2 => exact absurd rfl h1
  case twF4 => exact absurd rfl h2
  case twF4der => exact absurd rfl h3
  case B2der =>
    exfalso
    simp only [markChar] at hc
    exact absurd hc (by norm_num)
  case G2der =>
    exfalso
    simp only [markChar] at hc
    exact absurd hc (by norm_num)

end CFSG.StandardType
