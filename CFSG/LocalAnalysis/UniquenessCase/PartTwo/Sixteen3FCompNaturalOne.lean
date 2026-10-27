module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeClassicalComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeAlternatingComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLFourNaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLFiveNaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLSixSevenNaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6NaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneS1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltSixSevenNaturalR880
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltEightSLFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenListTwoOddRank
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem s16nt_concl163F_of_binarySL_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (_hs : 1 < s15 D.M V₀ V hV L)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    {n : ℕ} (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) n 1) :
    Concl163F D V₀ V hV L := by
  have hn3 : 3 ≤ n := s16k_three_le_of_isSLn hcomp.2.2 hSL
  by_cases hn8 : 8 ≤ n
  · exact (s168e3_false_of_sl_component_ge_eight c hcomp hn8 hSL).elim
  · have hn7 : n ≤ 7 := by omega
    interval_cases n
    · have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := by
        simpa [IsL3, IsLn] using s16k_isLn_of_isSLn (by norm_num) hSL
      exact (not_s15ListTwo_of_odd_pRank hodd (Or.inl hL3)).elim
    · exact s168e3_concl163F_of_naturalSL_four c hcomp hSL hN
    · exact s168e3_concl163F_of_naturalSL_five c hcomp hSL hN
    · exact s168e3_concl163F_of_naturalSL_six_seven c hcomp (Or.inl rfl) hSL hN
    · exact s168e3_concl163F_of_naturalSL_six_seven c hcomp (Or.inr rfl) hSL hN

theorem s16nt_concl163F_of_binarySp_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (_hs : 1 < s15 D.M V₀ V hV L)
    {n : ℕ} (hSp : IsSpn ↥(lBar V₀ V hV L) n 1)
    (hN : NatSpn (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) n 1) :
    Concl163F D V₀ V hV L := by
  have hn6 : 6 ≤ n := s16k_six_le_of_isSpn hcomp.2.2 hSp
  obtain ⟨k, hk⟩ := hSp.1
  by_cases hn8 : 8 ≤ n
  · exact (s168e3_false_of_sp_component_ge_eight c hcomp hn8 hSp).elim
  · have hn : n = 6 := by omega
    subst hn
    exact s168e3_concl163F_of_naturalSp_six c hcomp hSp hN

theorem s16nt_concl163F_of_binaryOmegaPlus_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    {n : ℕ} (hOp : IsOmegaPlus ↥(lBar V₀ V hV L) n 1) :
    Concl163F D V₀ V hV L := by
  have hn6 : 6 ≤ n := s16k_six_le_of_isOmegaPlus hcomp.2.2 hOp
  obtain ⟨k, hk⟩ := hOp.1
  by_cases hn8 : 8 ≤ n
  · exact (s168e3_false_of_omegaPlus_component_ge_eight c hcomp hn8 hOp).elim
  · have hn : n = 6 := by omega
    subst hn
    have hA8 : UC22.IsAlt ↥(lBar V₀ V hV L) 8 := s15k_omp6_isAlt8 hOp
    have hSL4 : IsSLn ↥(lBar V₀ V hV L) 4 1 := s16low_isSLn_of_isAlt_eight hA8
    have h1 : s15 D.M V₀ V hV L = 1 :=
      s15_eq_one_of_sl_four_component_at_three c hcomp hSL4
    exact False.elim (by omega)

theorem s16nt_concl163F_of_binaryOmegaMinus_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    {n : ℕ} (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) n 1) :
    Concl163F D V₀ V hV L := by
  have hn4 : 4 ≤ n := s16k_four_le_of_isOmegaMinus hcomp.2.2 hOm
  obtain ⟨k, hk⟩ := hOm.1
  by_cases hn10 : 10 ≤ n
  · exact (s168e3_false_of_omegaMinus_component_ge_ten c hcomp hn10 hOm).elim
  · have hn : n = 4 ∨ n = 6 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl
    · have hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5 := s16k_isAlt_five_of_isOmegaMinus_four hOm
      exact (not_s15ListTwo_of_odd_pRank hodd (Or.inr hA5)).elim
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s15_eq_one_of_omega_minus_six_component c hcomp hOm
      exact False.elim (by omega)
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s16nt_s15_eq_one_of_omega_minus_eight c hcomp hOm
      exact False.elim (by omega)

theorem s16nt_concl163F_of_binaryAlt_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    {n : ℕ} (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hN : AlternatingNatural (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) n) :
    Concl163F D V₀ V hV L := by
  have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hcomp.2.2 hA
  by_cases hn12 : 12 ≤ n
  · exact (s168e3_false_of_alternating_component_ge_twelve c hcomp hn12 hA).elim
  · have hn11 : n ≤ 11 := by omega
    interval_cases n
    · exact (not_s15ListTwo_of_odd_pRank hodd (Or.inr hA)).elim
    · exact s168e3_concl163F_of_alt_six_seven_natural_of_r880 c h880 hcomp hs
        (Or.inl rfl) hA hN
    · exact s168e3_concl163F_of_alt_six_seven_natural_of_r880 c h880 hcomp hs
        (Or.inr rfl) hA hN
    · have hSL4 : IsSLn ↥(lBar V₀ V hV L) 4 1 := s16low_isSLn_of_isAlt_eight hA
      have h1 : s15 D.M V₀ V hV L = 1 :=
        s15_eq_one_of_sl_four_component_at_three c hcomp hSL4
      exact False.elim (by omega)
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s16nt_s15_eq_one_of_alt_nine_eleven c hcomp (le_refl 9) (by norm_num) hA
      exact False.elim (by omega)
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s16nt_s15_eq_one_of_alt_nine_eleven c hcomp (by omega) (by omega) hA
      exact False.elim (by omega)
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s16nt_s15_eq_one_of_alt_nine_eleven c hcomp (by omega) (by omega) hA
      exact False.elim (by omega)

theorem s168e3_concl163F_of_sumOfNatShape_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 1) :
    Concl163F D V₀ V hV L := by
  rcases hsum with ⟨n, hSL | hSp | hOp | hOm | hAlt⟩
  · exact s16nt_concl163F_of_binarySL_one c hcomp hs hodd hSL.1
      (s16k_sumOfNat_one inf_le_left hSL.2)
  · exact s16nt_concl163F_of_binarySp_one c hcomp hs hSp.1
      (s16k_sumOfNat_one inf_le_left hSp.2)
  · exact s16nt_concl163F_of_binaryOmegaPlus_one c hcomp hs hOp.1
  · exact s16nt_concl163F_of_binaryOmegaMinus_one c hcomp hs hodd hOm.1
  · exact s16nt_concl163F_of_binaryAlt_one c h880 hcomp hs hodd hAlt.1
      (s16k_sumOfNat_one inf_le_left hAlt.2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
