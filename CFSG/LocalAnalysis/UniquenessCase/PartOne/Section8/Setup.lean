module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Core
public import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThreeStrong

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem three_mem_uniqueFourBeta_of_four_le_pRank {M : Subgroup G} (hM : IsTwoLocal M)
    (h4 : 4 ≤ CFSG.Open.pRank 3 M) : 3 ∈ CFSG.Open.uniqueFourBeta G := by
  have h3 : (3 : ℕ).Prime := by norm_num
  have hpos : 0 < CFSG.Open.pRank 3 M := by omega
  have hdvd : 3 ∣ Nat.card G :=
    CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank 3 h3 M hpos
  have hrank : CFSG.Open.pRank 3 M ≤ CFSG.Open.twoLocalPrimeRank 3 G :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove 3 h3)
      ⟨M, hM, rfl⟩
  refine ⟨h3, by norm_num, hdvd, ?_⟩
  show 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G
  omega

theorem pRank_three_le_three_of_not_strong (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M) :
    CFSG.Open.pRank 3 S.M ≤ 3 := by
  by_contra hle
  have h4 : 4 ≤ CFSG.Open.pRank 3 S.M := by omega
  have hβ : 3 ∈ CFSG.Open.uniqueFourBeta G :=
    three_mem_uniqueFourBeta_of_four_le_pRank S.maxLocal.1 h4
  exact hnot (CFSG.LocalAnalysis.UniquenessCase.UC22.isStronglyPEmbedded_three_of_mem_uniqueFourBeta
    hU S hσ hβ)

theorem isStronglyPEmbedded_of_mem_sigma_of_calC (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) {L : Subgroup G} (hL : L ∈ calC S.M) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma S.M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p S.M :=
  CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hL) hp

theorem hyp81_of_calC_of_three_le {M L : Subgroup G} (hL : L ∈ calC M)
    (h3 : 3 ≤ CFSG.Open.pRank 3 L) :
    CFSG.Yardstones.Mf4cdcdf2e013.Hyp81 M L := by
  obtain ⟨hsub, hperf, hquasi⟩ := hL
  refine ⟨hsub.le, hsub, hperf, h3, Or.inl ?_⟩
  exact ⟨inferInstance, hquasi⟩

theorem isStronglyPEmbedded_three_of_calC_three_le (hS : Standing4 G)
    (S : Setup4 G) (hPart : CFSG.Yardstones.Mf4cdcdf2e013.PartIAt S.M) {L : Subgroup G}
    (hL : L ∈ calC S.M) (h3 : 3 ≤ CFSG.Open.pRank 3 L) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M :=
  hPart.2.2 L (hyp81_of_calC_of_three_le hL h3)

theorem pRank_three_eq_two_of_mem_calC_of_list880 (hS : Standing4 G) (S : Setup4 G)
    (hPart : CFSG.Yardstones.Mf4cdcdf2e013.PartIAt S.M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M) {L : Subgroup G}
    (hL : L ∈ calC S.M) (h2 : 2 ≤ CFSG.Open.pRank 3 L) :
    CFSG.Open.pRank 3 L = 2 := by
  apply le_antisymm _ h2
  by_contra h
  have h3 : 3 ≤ CFSG.Open.pRank 3 L := by omega
  exact hnot (isStronglyPEmbedded_three_of_calC_three_le hS S hPart hL h3)

@[expose] def sec7CoreOf (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    {L : Subgroup G} (hL : L ∈ calC S.M) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma S.M) :
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4 G :=
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4.ofUnique hS hU S.M S.maxLocal p hp
    (isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL hp)

@[simp] theorem sec7CoreOf_M (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    {L : Subgroup G} (hL : L ∈ calC S.M) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma S.M) :
    (sec7CoreOf hS hU S hL hp).M = S.M := rfl

theorem three_dvd_center_bar2_of_calC_of_not_normal (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M) {L : Subgroup G}
    (hL : L ∈ calC S.M) (h2 : CFSG.Open.pRank 3 L = 2)
    (hnotN : ¬ S.M ≤ normalizer (L : Set G)) :
    3 ∣ Nat.card (Subgroup.center (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)) := by
  by_contra hZ
  obtain ⟨E, hEL, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
  rw [h2] at hEcard
  have h4 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.calCRankTwice S.M L hL hnotN
    3 (by norm_num) (by norm_num) hZ E hEL hEel 2 hEcard
  have hle := pRank_three_le_three_of_not_strong hS hU S hσ hnot
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
