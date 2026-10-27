module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalSmallRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallAxisNormalizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeG
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKPerfType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatMany
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s168e3_case153_2_of_small_natural
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) :
    Case153_2 D V₀ V hV L := by
  classical
  have hne1 : s15 D.M V₀ V hV L ≠ 1 := s168e3_s15_ne_one_of_listTwo c hperf hL2
  have hs1 : 1 ≤ s15 D.M V₀ V hV L := Om8Excl.one_le_s15 D.M V₀ V hV L
  have hs : 2 ≤ s15 D.M V₀ V hV L := by omega
  have hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    (s168e3_unique_of_natPerf_of_two_le_s15 c hcomp hperf hs).1
  have hshape : s15Shape D V₀ V hV L L := s168e3_shape_self_of_natPerf c hcomp hperf
  have hperf' : s15KNatPerf ↥(barSub V₀ V hV L)
      (barSub (v1Sub D.M V₀ V hV L) V hV L)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV L)) := by
    change s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L)
      (commSub ⊤ (lStar D.M V₀ V hV L))
    rw [s15_Three_commSub_top_lStar c.setting.hyp151 hV]
    exact hperf
  have hrs2 : s15Rs D V₀ V hV L L ≤ 2 :=
    s15_Three_rs_le_two h82 rSchur2_153_holds rSimple153_holds c.std.h127
      c.std.h119 c.std.h1217 c.setting.hyp151 hV hshape hperf' hL2 hns
  have hrs1 : s15Rs D V₀ V hV L L = 1 → 2 < mSub V₀ := by
    intro h1
    exact absurd ((s15_Three_rs_eq_one_iff D V₀ V hV L L).1 h1).2 hne1
  have hPT := rPerfType153_holds (V := Vtil (v1Sub D.M V₀ V hV L) V hV)
    (X := ↥(lBar V₀ V hV L))
    (K := barSub (v1Sub D.M V₀ V hV L) V hV L)
    (Z := commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV L)) hperf'
  rcases hL2 with hL3 | hA5
  ·
    have hsig : D.sig = {7} :=
      s168e3_sig_eq_of_small_natural c hcomp hperf hs (Or.inr ⟨rfl, hL3⟩)
    have hp : 7 ∈ D.sig := by
      rw [hsig]
      exact Set.mem_singleton 7
    have hrk : CFSG.Open.pRank 7 D.M = 3 := c.std.pRank_eq_three hp
    refine s15_Three_case_two_of 7 le_rfl ?_ hshape.2.2.1 hsig hrk hrs2 hrs1
    exact Or.inr ⟨rfl, hL3, hPT.1 hL3⟩
  ·
    have hsig : D.sig = {5} :=
      s168e3_sig_eq_of_small_natural c hcomp hperf hs (Or.inl ⟨rfl, hA5⟩)
    have hp : 5 ∈ D.sig := by
      rw [hsig]
      exact Set.mem_singleton 5
    have hrk : CFSG.Open.pRank 5 D.M = 3 := c.std.pRank_eq_three hp
    refine s15_Three_case_two_of 5 le_rfl ?_ hshape.2.2.1 hsig hrk hrs2 hrs1
    exact Or.inl ⟨rfl, hA5, hPT.2.1 hA5⟩

theorem s168e3_concl163F_of_sl_three_sum_one
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : s16h_H5L3Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 1) :
    Concl163F D V₀ V hV L := by
  classical
  have hLn : IsLn ↥(lBar V₀ V hV L) 3 1 :=
    s16k_isLn_of_isSLn (by norm_num) hrow.1
  have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := hLn
  have hNsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 1 :=
    s168e3_sumOfNat_binarySL_star c hrow.2
  have hNstar : BinaryNaturalSL (lStar D.M V₀ V hV L)
      (wStar D.M V₀ V hV L) ⊥ 3 1 :=
    s16k_sumOfNat_one bot_le hNsum
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inl ⟨3, by norm_num, hLn, hNstar⟩
  have hL2 : s15ListTwo ↥(lBar V₀ V hV L) := Or.inl hL3
  exact Or.inl (Or.inl (Or.inr (Or.inl
    (s168e3_case153_2_of_small_natural c h82 hcomp hperf hL2))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
