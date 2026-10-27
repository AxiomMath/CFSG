module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Ctx812
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (Ctx812 Ctx812E Setup812)

variable {G : Type} [Group G] [Finite G] {D : Data G}

abbrev Ctx82E3.C4Data (G : Type) [Group G] [Finite G] (M : Subgroup G) : Type :=
  Theorem82.C4Data G M

theorem Ctx82E3.three_not_mem_beta (c : Ctx82E3 D) : 3 ∉ uniqueFourBeta G := by
  rintro ⟨-, -, -, h4⟩
  have h := CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_le_evenRank (G := G) 3
    (by norm_num) (by norm_num)
  have h3 : evenRank G = 3 := c.rank
  have h4' : 4 ≤ rankThreeLocalRank 3 G := h4
  omega

@[expose] def Ctx82E3.toCtx812EOfSubset (c : Ctx82E3 D) (s : Set ℕ) (hs : s ⊆ D.sig) :
    Ctx812E G where
  k := 3
  three_le_k := le_rfl
  standing := D.standing
  S := ⟨D.M, D.maxLocal⟩
  sig := s
  sig_prime := fun p hp => D.sig_prime p (hs hp)
  rank_ge := fun p hp => c.three_le p (hs hp)
  four_le_imp_mem := fun r hr hr2 h4 =>
    absurd h4 (not_le.mpr (lt_of_le_of_lt (c.pRank_le_three hr hr2) (by norm_num)))
  strong := fun _ hp => c.isStronglyPEmbedded_of_mem_sigma (hs hp)
  u2 := fun p hp => c.u2 p (hs hp)
  rankK := fun p hp _ hHM h2 _ hq =>
    Section7.pRank_pPrimeCore_le_three_of_evenRank_le_three
      (le_of_eq c.rank) D.maxLocal.1 (D.sig_prime p (hs hp)).1
      (c.isStronglyPEmbedded_of_mem_sigma (hs hp))
      (fun D' hD' hD'2 h2' => c.u2 p (hs hp) _ ⟨D', hD', hD'2, rfl⟩ h2') hHM h2 hq
  theoremC := c.theoremC
  three_not_mem_beta := c.three_not_mem_beta
  not_rankThreeGamma_le_of_le_center := fun hP hE hEab hcard =>
    c.not_rankThreeGamma_le_of_le_center hP hE hEab hcard
  L := c.L
  hyp81 := c.hyp81
  not_strong := c.not_strong

@[expose] def Ctx82E3.toCtx812EOf (c : Ctx82E3 D) (X : Ctx82E3.C4Data G D.M) (s : Set ℕ)
    (hs : s ⊆ D.sig) : Ctx812E G :=
  Function.const (Ctx82E3.C4Data G D.M) (c.toCtx812EOfSubset s hs) X

@[expose] def Ctx82E3.toCtx812 (c : Ctx82E3 D) (X : Ctx82E3.C4Data G D.M) : Ctx812 G :=
  { c.toCtx812EOfSubset {p | p ∈ D.sig ∧ p ∣ ((c.L).subgroupOf D.M).index} (fun _ hp => hp.1) with
    dvd_index := fun _ hp _ => hp.2
    c4 := X }

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
