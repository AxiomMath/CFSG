module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 Hyp81 TheoremCAt Theorem614At)

variable {G : Type} [Group G] [Finite G]

structure Counterexample4 (G : Type) [Group G] [Finite G] where
  standing : Standing4 G
  unique : uniqueFourUnique G
  S : Setup4 G
  inMSigma : S.InMSigma
  theoremC : TheoremCAt S.M
  theorem614 : Theorem614At S.M
  L : Subgroup G
  hyp81 : Hyp81 S.M L
  not_strong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M

namespace Counterexample4

theorem L_ne_bot (c : Counterexample4 G) : c.L ≠ ⊥ := by
  intro hbot
  have h3 : 3 ≤ CFSG.Open.pRank 3 c.L := c.hyp81.2.2.2.1
  have h0 : CFSG.Open.pRank 3 c.L = 0 := by
    apply le_antisymm ?_ (Nat.zero_le _)
    apply CFSG.SectionRank.pRank_le (p := 3) (H := c.L) (k := 0) (by norm_num)
    intro E hE _
    have hEbot : E = ⊥ := by simpa [hbot] using hE
    rw [hEbot]
    simp
  omega

theorem not_isSolvable (c : Counterexample4 G) : ¬ Group.IsSolvable c.S.M := by
  intro hM
  haveI : Group.IsSolvable ↥c.S.M := hM
  haveI : Nontrivial ↥c.L := (Subgroup.nontrivial_iff_ne_bot c.L).mpr (L_ne_bot c)
  haveI : Group.IsSolvable ↥c.L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion c.hyp81.1)
      (Subgroup.inclusion_injective c.hyp81.1)
  have hcomm : commutator ↥c.L = ⊤ := by
    apply Subgroup.map_injective c.L.subtype_injective
    rw [Subgroup.map_subtype_commutator, c.hyp81.2.2.1, Subgroup.map_top, c.L.range_subtype]
  have hlt : commutator ↥c.L < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥c.L)
  rw [hcomm] at hlt
  exact (lt_irrefl (⊤ : Subgroup ↥c.L)) hlt

theorem isStronglyPEmbedded_of_mem_sigma (c : Counterexample4 G) {p : ℕ}
    (hp : p ∈ uniqueFourSigma c.S.M) : IsStronglyPEmbedded p c.S.M := by
  obtain ⟨-, hM0, -, P, hPM, hΓ, hcl⟩ :=
    (c.unique c.S.M c.S.maxLocal ⟨p, hp⟩).1 p hp
  rcases hcl with ⟨hdvd, hstrong⟩ | ⟨-, hsolv, -, -⟩
  · exact CFSG.LocalAnalysis.UniquenessCase.UC6.isStronglyPEmbedded_of_clause_one hM0 hdvd hstrong
  · exact absurd hsolv (not_isSolvable c)

theorem three_not_mem_sigma (c : Counterexample4 G) : 3 ∉ uniqueFourSigma c.S.M :=
  fun h3 => c.not_strong (isStronglyPEmbedded_of_mem_sigma c h3)

theorem three_not_mem_beta (c : Counterexample4 G) : 3 ∉ uniqueFourBeta G := by
  intro h3
  have hp3 : c.S.p = 3 := c.inMSigma.1 h3
  exact three_not_mem_sigma c (hp3 ▸ c.S.hp)

theorem pRank_three_M (c : Counterexample4 G) : CFSG.Open.pRank 3 c.S.M = 3 := by
  have h3prime : (3 : ℕ).Prime := by norm_num
  have h3dvdG : 3 ∣ Nat.card G :=
    CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank 3 h3prime c.L
      (by have := c.hyp81.2.2.2.1; omega)
  have hle3 : CFSG.Open.pRank 3 c.S.M ≤ 3 := by
    have hrank : CFSG.Open.pRank 3 c.S.M ≤ uniqueFourTwoLocalRank 3 G :=
      le_csSup (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove 3 h3prime)
        ⟨c.S.M, c.S.maxLocal.1, rfl⟩
    have hnot4 : ¬ 4 ≤ uniqueFourTwoLocalRank 3 G := by
      intro h4
      exact three_not_mem_beta c ⟨h3prime, by norm_num, h3dvdG, h4⟩
    omega
  have hge3 : 3 ≤ CFSG.Open.pRank 3 c.S.M :=
    c.hyp81.2.2.2.1.trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3prime c.hyp81.1)
  omega

theorem pRank_three_L (c : Counterexample4 G) : CFSG.Open.pRank 3 c.L = 3 := by
  apply le_antisymm
  · exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 (by norm_num) c.hyp81.1).trans
      (pRank_three_M c).le
  · exact c.hyp81.2.2.2.1

theorem sigma_nonempty (c : Counterexample4 G) : (uniqueFourSigma c.S.M).Nonempty :=
  ⟨c.S.p, c.S.hp⟩

theorem five_le_of_mem_sigma (c : Counterexample4 G) {p : ℕ}
    (hp : p ∈ uniqueFourSigma c.S.M) : 5 ≤ p := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact three_not_mem_sigma c hp
  exact Nat.Prime.five_le_of_ne_two_of_ne_three hp.1.1 hp.1.2.1 hp3

theorem four_le_pRank_of_mem_sigma (c : Counterexample4 G) {p : ℕ}
    (hp : p ∈ uniqueFourSigma c.S.M) : 4 ≤ CFSG.Open.pRank p c.S.M :=
  CFSG.LocalAnalysis.UniquenessCase.UC6.four_le_pRank_of_sigma hp

theorem M_ne_top (c : Counterexample4 G) : c.S.M ≠ ⊤ := by
  haveI := c.standing.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top c.standing.nonab c.S.maxLocal.1

theorem sigma_subset_sigmaOne (c : Counterexample4 G) :
    CFSG.Open.uniqueFourSigma c.S.M ⊆ CFSG.Yardstones.Mf4cdcdf2e013.SigmaOne4 G := by
  intro p hp
  exact ⟨hp.1, c.S.M, c.S.maxLocal, hp, isStronglyPEmbedded_of_mem_sigma c hp⟩

theorem not_rankThreeGamma_le_of_le_center (c : Counterexample4 G) {P E : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M)
    (hE : E ≤ P ⊓ Subgroup.centralizer (P : Set G)) (hEab : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) :
    ¬ CFSG.Open.rankThreeGamma 1 3 E ≤ c.S.M := by
  intro hΓ
  exact c.not_strong
    (c.theorem614 (sigma_subset_sigmaOne c) 3 (by norm_num) (by norm_num)
      (three_not_mem_sigma c) P hP E hE hEab hcard hΓ)

end Counterexample4

theorem theorem82Four_of_isEmpty
    (h : ∀ (G : Type) [Group G] [Finite G], Counterexample4 G → False) :
    CFSG.Yardstones.Mf4cdcdf2e013.Theorem82Four := by
  intro G instG instFin standing unique S inMSigma theoremC theorem614
  intro L hyp81
  by_contra hnotstrong
  exact h G ⟨standing, unique, S, inMSigma, theoremC, theorem614, L, hyp81, hnotstrong⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
