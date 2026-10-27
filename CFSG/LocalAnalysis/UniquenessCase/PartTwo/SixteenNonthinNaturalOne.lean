module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallAlternatingNaturalOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenListTwoOddRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeClassicalComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeAlternatingComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLFourNaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLFiveNaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLSixSevenNaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6NaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmega6NaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneOmegaRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltNineNaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltTenElevenNaturalRow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_concl163F_of_nonthin_sum_one_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 1)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 1) :
    Concl163F D V₀ V hV L := by
  rcases hsum with ⟨n, hSL | hSp | hOp | hOm | hAlt⟩
  ·
    obtain ⟨hSLn, hsum⟩ := hSL
    have hn3 : 3 ≤ n := s16k_three_le_of_isSLn hcomp.2.2 hSLn
    by_cases hn8 : 8 ≤ n
    · exact (s168e3_false_of_sl_component_ge_eight c hcomp hn8 hSLn).elim
    · have hn7 : n ≤ 7 := by omega
      interval_cases n
      · have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := by
          simpa [IsL3, IsLn] using s16k_isLn_of_isSLn (by norm_num) hSLn
        exact (not_s15ListTwo_of_odd_pRank hodd (Or.inl hL3)).elim
      · exact s168e3_concl163F_of_naturalSL_four c hcomp hSLn
          (s16k_sumOfNat_one inf_le_left hsum)
      · exact s168e3_concl163F_of_naturalSL_five c hcomp hSLn
          (s16k_sumOfNat_one inf_le_left hsum)
      · exact s168e3_concl163F_of_naturalSL_six_seven c hcomp (Or.inl rfl) hSLn
          (s16k_sumOfNat_one inf_le_left hsum)
      · exact s168e3_concl163F_of_naturalSL_six_seven c hcomp (Or.inr rfl) hSLn
          (s16k_sumOfNat_one inf_le_left hsum)
  ·
    obtain ⟨hSpn, hsum⟩ := hSp
    have hn6 : 6 ≤ n := s16k_six_le_of_isSpn hcomp.2.2 hSpn
    by_cases hn8 : 8 ≤ n
    · exact (s168e3_false_of_sp_component_ge_eight c hcomp hn8 hSpn).elim
    · obtain ⟨k, hk⟩ := hSpn.1
      have hn : n = 6 := by omega
      subst hn
      exact s168e3_concl163F_of_naturalSp_six c hcomp hSpn
        (s16k_sumOfNat_one inf_le_left hsum)
  ·
    obtain ⟨hOpn, hsum⟩ := hOp
    have hn6 : 6 ≤ n := s16k_six_le_of_isOmegaPlus hcomp.2.2 hOpn
    by_cases hn8 : 8 ≤ n
    · exact (s168e3_false_of_omegaPlus_component_ge_eight c hcomp hn8 hOpn).elim
    · obtain ⟨k, hk⟩ := hOpn.1
      have hn : n = 6 := by omega
      subst hn
      exact s168e3_concl163F_of_omegaPlus_six_natural_of_s_eq_one c hs hOpn
        (s16k_sumOfNat_one inf_le_left hsum)
  ·
    obtain ⟨hOmn, hsum⟩ := hOm
    have hn4 : 4 ≤ n := s16k_four_le_of_isOmegaMinus hcomp.2.2 hOmn
    by_cases hn10 : 10 ≤ n
    · exact (s168e3_false_of_omegaMinus_component_ge_ten c hcomp hn10 hOmn).elim
    · obtain ⟨k, hk⟩ := hOmn.1
      have hn : n = 4 ∨ n = 6 ∨ n = 8 := by omega
      rcases hn with rfl | rfl | rfl
      · have hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5 :=
          s16k_isAlt_five_of_isOmegaMinus_four hOmn
        exact (not_s15ListTwo_of_odd_pRank hodd (Or.inr hA5)).elim
      · exact concl163F_of_omega_minus_six_natural c hcomp hOmn
          (by simpa only [wTil, lBar] using s16k_sumOfNat_one inf_le_left hsum)
      · exact s16nt_concl163F_of_natural_omega_minus_eight c hcomp hOmn
          (s16k_sumOfNat_one inf_le_left hsum)
  ·
    obtain ⟨hAn, hsum⟩ := hAlt
    have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hcomp.2.2 hAn
    by_cases hn12 : 12 ≤ n
    · exact (s168e3_false_of_alternating_component_ge_twelve c hcomp hn12 hAn).elim
    · have hn11 : n ≤ 11 := by omega
      interval_cases n
      · exact (not_s15ListTwo_of_odd_pRank hodd (Or.inr hAn)).elim
      · exact s168e3_concl163F_of_small_alternating_natural_of_s_eq_one c hs (Or.inl rfl)
          hAn (s16k_sumOfNat_one inf_le_left hsum)
      · exact s168e3_concl163F_of_small_alternating_natural_of_s_eq_one c hs
          (Or.inr (Or.inl rfl)) hAn (s16k_sumOfNat_one inf_le_left hsum)
      · exact s168e3_concl163F_of_small_alternating_natural_of_s_eq_one c hs
          (Or.inr (Or.inr rfl)) hAn (s16k_sumOfNat_one inf_le_left hsum)
      · exact s16nt_concl163F_of_natural_alt_nine c hcomp hAn
          (s16k_sumOfNat_one inf_le_left hsum)
      · exact s16nt_concl163F_of_natural_alt_ten_eleven c hcomp (by omega) (by omega) hAn
          (s16k_sumOfNat_one inf_le_left hsum)
      · exact s16nt_concl163F_of_natural_alt_ten_eleven c hcomp (by omega) (by omega) hAn
          (s16k_sumOfNat_one inf_le_left hsum)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
