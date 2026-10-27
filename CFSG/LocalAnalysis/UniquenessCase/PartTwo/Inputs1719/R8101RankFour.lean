module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100R
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UProof
public import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS3
public import CFSG.LocalAnalysis.UniquenessCase.UC7R76Four
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XI
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Sz
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6U4OverAux1
import CFSG.Quasithin.Vol2.Ch10SecAShape
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCheap
public import CFSG.LocalAnalysis.WeakClosure81.SuzukiGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem isSz_param_unique {X : Type} [Group X] {a b : ℕ}
    (ha : IsSz X a) (hb : IsSz X b) : a = b := by
  obtain ⟨a', -, rfl, ⟨ea⟩⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_mulEquiv_sz_of_isSz ha
  obtain ⟨b', -, rfl, ⟨eb⟩⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_mulEquiv_sz_of_isSz hb
  have h := (Nat.card_congr ea.toEquiv).symm.trans (Nat.card_congr eb.toEquiv)
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz,
    CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz] at h
  have hodd : ∀ k : ℕ, Odd (((2 ^ (2 * k + 1)) ^ 2 + 1) * (2 ^ (2 * k + 1) - 1)) := by
    intro k
    have hev : Even (2 ^ (2 * k + 1)) := (Nat.even_pow' (by omega)).mpr even_two
    exact ((Nat.even_pow' two_ne_zero).mpr hev).add_one.mul
      (Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one)
  have e : 2 ^ (2 * (2 * a' + 1)) * (((2 ^ (2 * a' + 1)) ^ 2 + 1) * (2 ^ (2 * a' + 1) - 1)) =
      2 ^ (2 * (2 * b' + 1)) * (((2 ^ (2 * b' + 1)) ^ 2 + 1) * (2 ^ (2 * b' + 1) - 1)) := by
    rw [mul_comm 2 (2 * a' + 1), mul_comm 2 (2 * b' + 1), pow_mul, pow_mul, ← mul_assoc,
      ← mul_assoc, h]
  have := (CFSG.Quasithin.Vol2.Ch10.SecA.two_pow_mul_odd_inj (hodd a') (hodd b') e).1
  omega

theorem r_eq_seven_of_case8100Three {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ}
    {r p : ℕ} {A X : Subgroup G} (hH : Hyp8100 D L n r p A X) (hc : Case8100ThreeR D L p X) :
    r = 7 := by
  obtain ⟨-, -, hshape, hr, hdvd, -⟩ := hH
  obtain ⟨-, hL2, -⟩ := hc
  have hn0 : n 0 = 3 := by
    rcases hshape 0 with h | h
    · exact PartTwo.s16c6_isL2_param_unique h hL2
    · exact (P2214S.false_of_isSz_of_isL2 h hL2).elim
  rw [hn0] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (n 1)) with h | h
  · rw [h] at hdvd
    have h1 : r ∣ 1 := by simpa using hdvd
    exact absurd (Nat.dvd_one.1 h1) hr.one_lt.ne'
  · rw [h] at hdvd
    have h7 : r ∣ 7 := by simpa using hdvd
    exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h7

theorem r_eq_thirtyOne_of_case8100Four {D : Data G}
    {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X : Subgroup G}
    (hH : Hyp8100 D L n r p A X) (hc : Case8100FourR D L p X) : r = 31 := by
  obtain ⟨-, -, hshape, hr, hdvd, -⟩ := hH
  obtain ⟨-, hSz, -⟩ := hc
  have hn0 : n 0 = 5 := by
    rcases hshape 0 with h | h
    · exact (P2214S.false_of_isSz_of_isL2 hSz h).elim
    · exact isSz_param_unique h hSz
  rw [hn0] at hdvd
  rcases (Nat.dvd_prime Nat.prime_five).1 (Nat.gcd_dvd_left 5 (n 1)) with h | h
  · rw [h] at hdvd
    have h1 : r ∣ 1 := by simpa using hdvd
    exact absurd (Nat.dvd_one.1 h1) hr.one_lt.ne'
  · rw [h] at hdvd
    have h31 : r ∣ 31 := by simpa using hdvd
    exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h31

theorem u4x_of_case8100Three {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ}
    {A X : Subgroup G} (hH : Hyp8100 D L n r p A X) (hc : Case8100ThreeR D L p X) :
    U4X D (L 0) (L 1) 3 := by
  obtain ⟨hcal, hne, -, -, -, hpσ, -⟩ := hH
  obtain ⟨hset, hL2, rfl, -⟩ := hc
  have hsetC : conjSetOf D.M (L 0) = {L 0, L 1} := hset.symm
  exact ⟨hcal 0, hcal 1, hne.symm, hsetC, by rw [hsetC]; exact Set.ncard_pair hne,
    Or.inl ⟨rfl, hL2⟩, hpσ⟩

theorem u4x_of_case8100Four {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ}
    {A X : Subgroup G} (hH : Hyp8100 D L n r p A X) (hc : Case8100FourR D L p X) :
    U4X D (L 0) (L 1) 5 := by
  obtain ⟨hcal, hne, -, -, -, hpσ, -⟩ := hH
  obtain ⟨hset, hSz, rfl, -⟩ := hc
  have hsetC : conjSetOf D.M (L 0) = {L 0, L 1} := hset.symm
  exact ⟨hcal 0, hcal 1, hne.symm, hsetC, by rw [hsetC]; exact Set.ncard_pair hne,
    Or.inr ⟨rfl, hSz⟩, hpσ⟩

theorem mem_uniqueSet_of_u4x
    {D : Data G} {L K : Subgroup G} {n : ℕ} (u : U4X D L K n) (hSg : UC6S846.SigmaStd D)
    (hfour : ∀ q ∈ D.sig, 4 ≤ CFSG.Open.pRank q D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ q ∈ D.sig, IsStronglyPEmbedded q D.M → Conclusion76 D.M q) (h847 : R847 D)
    (h869 : R869NS5 D) (hGL : GL3Excl.GL3Excl) (he : 3 < CFSG.Open.evenRank G)
    {A : Subgroup G} (hAL : A ≤ L) (hA : Nat.card A = 2 ^ n - 1) : A ∈ uniqueSet D.M := by
  have hr : (2 ^ n - 1).Prime := u.prime_r
  have : Fact (2 ^ n - 1).Prime := ⟨hr⟩
  by_cases hspr : IsStronglyPEmbedded (2 ^ n - 1) D.M
  · refine uc22p22r_mem_uniqueSet_of_sp D hr hspr (hAL.trans u.hL.1.le)
      (IsPGroup.of_card (n := 1) (by rw [hA, pow_one])) ?_
    rintro rfl
    rw [Subgroup.card_bot] at hA
    exact hr.one_lt.ne hA
  · have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC u.hL) u.hσ
    exact u.u81_mem_uniqueSet_of_residual hSg hfour h614 h76 h847 he hspr
      (fun _ _ hR hBR hRB hBel hΩ hr3 hC1 hB0 hdvd =>
        u.u81_normalizer_le hsp (hfour n u.hσ) h847 he h869 hGL hR hBR hRB hBel hΩ hr3 hC1 hB0
          hdvd)
      hAL hA

theorem mem_uniqueSet_of_u4x_setup4
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSS : PartOne.Section7.StronglyEmbeddedSolvable)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hGL : GL3Excl.GL3Excl) (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) (h847 : R847 (UC6.dataOfSetup4 hS hU S))
    {L K : Subgroup G} {n : ℕ} (u : U4X (UC6.dataOfSetup4 hS hU S) L K n)
    (he : 3 < CFSG.Open.evenRank G) {A : Subgroup G} (hAL : A ≤ L)
    (hA : Nat.card A = 2 ^ n - 1) : A ∈ uniqueSet (UC6.dataOfSetup4 hS hU S).M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  have hfour : ∀ q ∈ (UC6.dataOfSetup4 hS hU S).sig,
      4 ≤ CFSG.Open.pRank q (UC6.dataOfSetup4 hS hU S).M :=
    fun _ hq => UC6.four_le_pRank_of_sigma hq
  have h614 : UC6.R6_14 (UC6.dataOfSetup4 hS hU S) :=
    (UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1
  have h76 := UC6.r76_dataOfSetup4 hSE hSE3 hB hS hU S hMS hPart
  have h869 := UC6.r869NS5_dataOfSetup4_of_inMSigma hSS hSE hSE3 hB hS hU S hMS
  have h76' : ∀ q ∈ (UC6.dataOfSetup4 hS hU S).sig,
      IsStronglyPEmbedded q (UC6.dataOfSetup4 hS hU S).M →
        Conclusion76 (UC6.dataOfSetup4 hS hU S).M q :=
    fun q hq hsp => h76 q ((UC6.dataOfSetup4 hS hU S).sig_prime q hq).1
      ((UC6.dataOfSetup4 hS hU S).sig_prime q hq).2 hsp
  exact mem_uniqueSet_of_u4x u hSg hfour h614 h76' h847 h869 hGL he hAL hA

theorem mem_uniqueSet_case8100Three_setup4
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSS : PartOne.Section7.StronglyEmbeddedSolvable)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hGL : GL3Excl.GL3Excl) (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) (h847 : R847 (UC6.dataOfSetup4 hS hU S))
    {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X : Subgroup G}
    (hH : Hyp8100 (UC6.dataOfSetup4 hS hU S) L n r p A X)
    (hc : Case8100ThreeR (UC6.dataOfSetup4 hS hU S) L p X) {A' : Subgroup G}
    (hA'L : A' ≤ L 0 ∨ A' ≤ L 1) (hA' : Nat.card A' = 7) :
    A' ∈ uniqueSet (UC6.dataOfSetup4 hS hU S).M := by
  have u := u4x_of_case8100Three hH hc
  have he : 3 < CFSG.Open.evenRank G := hc.2.2.2.1
  have hA7 : Nat.card A' = 2 ^ 3 - 1 := hA'.trans (by norm_num)
  rcases hA'L with h | h
  · exact mem_uniqueSet_of_u4x_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 u he h hA7
  · exact mem_uniqueSet_of_u4x_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 u.symm he h
      hA7

theorem r8101Three_setup4
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSS : PartOne.Section7.StronglyEmbeddedSolvable)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hGL : GL3Excl.GL3Excl) (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) (h847 : R847 (UC6.dataOfSetup4 hS hU S)) :
    ∀ (L : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (r p : ℕ) (A X : Subgroup G),
      Hyp8100 (UC6.dataOfSetup4 hS hU S) L n r p A X →
        Case8100ThreeR (UC6.dataOfSetup4 hS hU S) L p X →
          A ∈ uniqueSet (UC6.dataOfSetup4 hS hU S).M := by
  intro L n r p A X hH hc
  have h7 := r_eq_seven_of_case8100Three hH hc
  exact mem_uniqueSet_case8100Three_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 hH hc
    hH.2.2.2.2.2.2.2.1 (hH.2.2.2.2.2.2.1.trans h7)

theorem r8101Four_setup4
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSS : PartOne.Section7.StronglyEmbeddedSolvable)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hGL : GL3Excl.GL3Excl) (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) (h847 : R847 (UC6.dataOfSetup4 hS hU S)) :
    ∀ (L : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (r p : ℕ) (A X : Subgroup G),
      Hyp8100 (UC6.dataOfSetup4 hS hU S) L n r p A X →
        Case8100FourR (UC6.dataOfSetup4 hS hU S) L p X →
          A ∈ uniqueSet (UC6.dataOfSetup4 hS hU S).M := by
  intro L n r p A X hH hc
  have u := u4x_of_case8100Four hH hc
  have he : 3 < CFSG.Open.evenRank G := hc.2.2.2.1
  have hA : Nat.card A = 2 ^ 5 - 1 :=
    hH.2.2.2.2.2.2.1.trans ((r_eq_thirtyOne_of_case8100Four hH hc).trans (by norm_num))
  rcases hH.2.2.2.2.2.2.2.1 with h | h
  · exact mem_uniqueSet_of_u4x_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 u he h hA
  · exact mem_uniqueSet_of_u4x_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 u.symm he h hA

theorem r8101_setup4
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSS : PartOne.Section7.StronglyEmbeddedSolvable)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hGL : GL3Excl.GL3Excl) (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) (h847 : R847 (UC6.dataOfSetup4 hS hU S)) :
    F08.R8101R (UC6.dataOfSetup4 hS hU S) := by
  intro L n r p A X hH hc
  rcases hc with hc | hc
  · exact r8101Three_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 L n r p A X hH hc
  · exact r8101Four_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 L n r p A X hH hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
