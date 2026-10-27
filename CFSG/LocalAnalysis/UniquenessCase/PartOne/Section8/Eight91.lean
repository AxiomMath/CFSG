module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91XShape
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Classes
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91X1Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91CentAZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Ranks
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91NormA
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91NormZLe
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91NormZCong
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91A94Reduce
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91A94Klc
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91A94Contra
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91HGammaO3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91HNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91HRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91HCompEx
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91HCompLe
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91HCompNotLe
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91YbarQS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91List
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91G211
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91FinalHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91NotSL3Core
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91PrimeCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91ThreeRankCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91OutCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R72 R76Sig)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.LocalAnalysis.UniquenessCase.UCK (K33 K34)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 (LieSporSimple)

theorem r891_pRank_three_le {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hns : ¬ IsStronglyPEmbedded 3 D.M) :
    CFSG.Open.pRank 3 D.M ≤ 3 := by
  by_contra h
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := by omega
  have h3 : 3 ∈ D.sig := hSg.four_mem 3 Nat.prime_three (by norm_num) h4
  exact hns (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) h3)

theorem r891_not_gamma_le {G : Type} [Group G] [Finite G] (D : Data G) (h856 : R856 D)
    (hNot : R891NotSL3Core) (L S : Subgroup G) (n : ℕ) (hset : R891Set D L S n)
    (hbasic : R891Basic D L S) : ¬ rankThreeGamma 1 3 (S ⊓ L) ≤ D.M := by
  intro hΓ
  rcases h856 L hset.mem hbasic.rank (S ⊓ L) hbasic.sylowL hΓ with hs | hsl
  · exact hset.notStrong hs
  · exact hNot (Bar2 L) n hset.d4 hsl

theorem r891_of_inputs
    {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (h63 : UC6.R6_3 D)
    (h72 : R72 D)
    (h76 : R76Sig D) (h856 : R856 D) : R891 D := by
  intro L hL n hd4
  by_contra hnot
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 D.M) := inferInstance
  have hS : IsSylowOf 3 (Q.map D.M.subtype) D.M := ⟨Q, rfl⟩
  have hset : R891Set D L (Q.map D.M.subtype) n := ⟨hL, hd4, hnot, hS⟩
  generalize Q.map D.M.subtype = S at hset
  have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 := r891_pRank_three_le D hSg hL hnot
  have hbasic : R891Basic D L S := s891_basic D hM3 L S n hset
  obtain ⟨R, hR⟩ := s891_x_shape D L S n hset hbasic
  obtain ⟨A, hAR, hAcl⟩ := s891_classes D L S n hset hbasic R hR
  have hX1 : R891X1Shape L A n := s891_x1_shape D L S A n hset hbasic hAcl
  have hctx : R891Ctx D L S n R A := ⟨hR, hAcl, hX1, hAR⟩
  have hΓ : ¬ rankThreeGamma 1 3 (S ⊓ L) ≤ D.M := r891_not_gamma_le D h856 r891NotSL3Core_holds L S n hset hbasic
  have hcent : R891CentRank D L S A :=
    s891_cent_az D hSg h63 h76 L S R A n hset hbasic hctx hΓ
  have hrank : R891Rank893 D L := s891_rank D hSg r891OutCore_holds r891PrimeCore_holds L S R A n hset hbasic hctx hcent
  have hnormA : R891NormA D A :=
    s891_norm_a D hSg h72 r891PrimeCore_holds L S R A n hset hbasic hctx hrank
  have hnotle : R891NotLe D L S :=
    s891_norm_z_not_le D hSg h63 L S R A n hset hbasic hctx hrank hnormA hΓ
  have hcong : R891Cong D n :=
    s891_norm_z_cong D hSg h72 r891PrimeCore_holds L S R A n hset hbasic hctx hrank hnotle
  have h893 : R891Facts893 D L S A n := ⟨hrank, hnormA, hcong, hnotle⟩
  have hA : A ∈ uniqueSet D.M := by
    by_contra hnotA
    obtain ⟨K, K₀, hcfg⟩ := s891_a94_reduce D hSg L S A n hset hbasic hAcl h893 hnotA
    have hKLC : K ≤ L ⊔ CentOverO2 D.M L := s891_a94_klc D r891OutCore_holds L S A K K₀ n hset hbasic hcfg
    exact s891_a94_contra D hM3 r891ThreeRankCore_holds L S A K K₀ n hset hbasic hAcl hX1 hcfg hKLC
  have hst : R891State D L S R A n := ⟨hset, hbasic, hctx, h893, hA⟩
  have hnorm : R891Norm895 D L S n := s891_h_norm D L S n hset hbasic
  have hgam : R891Gamma895 D L S R := s891_h_gamma_o3 D L S R A n hst
  have hH3 : CFSG.Open.pRank 3 (R891H L S) ≤ 3 := s891_h_rank D hM3 L S R A n hst
  have hn1 : 1 ≤ n := hd4.admissible.2.1
  have hcomp : R891Comp895 D L S n R := by
    by_cases hn : n = 1
    · subst hn
      exact r891Gap211_holds D L S R A hst hgam hnorm
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨Ys, hc, h3, hnc⟩ := s891_h_comp_ex D L S R A n hn2 hst hnorm
      have hle := s891_h_comp_le D L S R A n hn2 hst hnorm hH3 Ys hc h3 hnc
      obtain ⟨hR, hnm, hz⟩ := s891_h_comp_not_le D L S R A n hn2 hst hgam Ys hc hle
      exact ⟨Ys, ⟨hc, fun _ => hle, hR, hnm, hz, fun h => absurd h hn⟩⟩
  have h895 : R891Facts895 D L S n R := ⟨hgam, hnorm, hcomp⟩
  obtain ⟨Ys, hY⟩ := hcomp
  have hYH : R891Y (R891H L S) (R891Z L S) Ys ≤ R891H L S :=
    (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hY3 : CFSG.Open.pRank 3 (R891Y (R891H L S) (R891Z L S) Ys) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hYH).trans hH3
  have hqs : R891YbarQS (R891H L S) (R891Z L S) Ys := s891_ybar_qs D L S R n hbasic Ys hY
  have h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys) :=
    s891_list896 (R891H L S) (R891Z L S) Ys hqs hY3
  exact r891_final_of_list896 hSg hst h895 hY h896

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
