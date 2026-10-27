module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNonthinIrreducibleSOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeStrongSeven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeSLSixSeven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLFiveThreeNatural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen3FCompDispatch
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltNineTripleNatural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltTripleThreeNatural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatSmallCounts
public import Certificates.Certificate431004
public import Certificates.Certificate17430
public import Certificates.Certificate9726
import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.HardMathSupport.Cooperstein.Proving.KerCommutatorFix
import CFSG.HardMathSupport.GuralnickMalle.CyclicTwo
import CFSG.LieType.Universal.Spin
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Alt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ChiOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Q1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeCovers
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UBar
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251K
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251i
import CFSG.RankThree.PartOne.TAIL.KSideCen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_concl163F_of_nonthin_component_of_s15_eq_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D) (h869 : F08.R869 D) (h880 : F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 1)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L)) :
    Concl163F D V₀ V hV L := by
  have hL3 : ¬ IsSLn ↥(lBar V₀ V hV L) 3 1 := fun hSL =>
    not_s15ListTwo_of_odd_pRank hodd (Or.inl (s16k_isLn_of_isSLn (by norm_num) hSL))
  have hA5 : ¬ UC22.IsAlt ↥(lBar V₀ V hV L) 5 := fun hA =>
    not_s15ListTwo_of_odd_pRank hodd (Or.inr hA)
  obtain ⟨t, -, -, -, htrk, -, -, hbranch⟩ := c.conc
  rcases hbranch with h133 | hprod | hnat | hirr
  ·
    rcases concl163F_or_cyclic_three_rank_six_s1_of_conc4_133 c h133 with h | ⟨hcyc, -, -⟩
    · exact h
    · have : Group.IsPerfect ↥(lBar V₀ V hV L) := Group.isPerfect_def.mpr hcomp.2.2.1
      have : Nontrivial ↥(lBar V₀ V hV L) := CFSG.LocalCores.isQuasisimple_nontrivial
        ((CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥(lBar V₀ V hV L))).mpr hcomp.2.2)
      have : IsCyclic ↥(lBar V₀ V hV L) := hcyc.1
      exact (Group.IsPerfect.not_isMulCommutative ↥(lBar V₀ V hV L) inferInstance).elim
  ·
    rcases hprod with ⟨K, hK, g, hg, hKgne, hEq, -⟩
    have hKg : IsComponentOf (K.map (MulAut.conj g).toMonoidHom) (Mbar D.M V₀ V hV) :=
      CFSG.Quasithin.F918V5G.isComponentOf_map_conj hK hg
    exact (false_of_isComponentOf_sup_of_distinct_components hcomp hK hKg hKgne hEq).elim
  ·
    rcases hnat with ⟨-, hsum3, htrans⟩
    obtain ⟨k, hk3, hshape⟩ := (sumOfAtMostThreeNat_iff (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))).mp hsum3
    interval_cases k
    · rcases hshape with ⟨n, hSL | hSp | hOp | hOm | hAlt⟩
      · exact (s168e3_false_of_sumOfNat_zero c hcomp hSL.2).elim
      · exact (s168e3_false_of_sumOfNat_zero c hcomp hSp.2).elim
      · exact (s168e3_false_of_sumOfNat_zero c hcomp hOp.2).elim
      · exact (s168e3_false_of_sumOfNat_zero c hcomp hOm.2).elim
      · exact (s168e3_false_of_sumOfNat_zero c hcomp hAlt.2).elim
    · exact s168e3_concl163F_of_nonthin_sum_one_of_s_eq_one c hcomp hs hodd hshape
    · exact s168e3_concl163F_of_sumOfNatShape_two c hcomp hshape
    · have hsum := hshape
      rcases hshape with ⟨n, ⟨hSL, -⟩ | ⟨hSp, -⟩ | ⟨hOp, -⟩ | ⟨hOm, -⟩ | ⟨hA, -⟩⟩
      · have hn3 : 3 ≤ n := s16k_three_le_of_isSLn hcomp.2.2 hSL
        by_cases hn8 : 8 ≤ n
        · exact (s168e3_false_of_sl_component_ge_eight c hcomp hn8 hSL).elim
        · interval_cases n
          · exact (hL3 hSL).elim
          · exact (s168e3_false_of_sum_three_sl_four_of_r880 c h880 hcomp hsum htrans hs hSL).elim
          · exact (s168e3_false_of_sum_three_sl_five c h880 hcomp hsum htrans hSL).elim
          · exact (s168e3_false_of_sum_three_sl_six_seven c hcomp hsum htrans hs
              (Or.inl rfl) hSL).elim
          · exact (s168e3_false_of_sum_three_sl_six_seven c hcomp hsum htrans hs
              (Or.inr rfl) hSL).elim
      · have hn6 : 6 ≤ n := s16k_six_le_of_isSpn hcomp.2.2 hSp
        obtain ⟨j, hj⟩ := hSp.1
        by_cases hn8 : 8 ≤ n
        · exact (s168e3_false_of_sp_component_ge_eight c hcomp hn8 hSp).elim
        · obtain rfl : n = 6 := by omega
          exact (s168e3_false_of_sum_three_sp_six c hcomp hsum htrans hs hSp).elim
      · have hn6 : 6 ≤ n := s16k_six_le_of_isOmegaPlus hcomp.2.2 hOp
        obtain ⟨j, hj⟩ := hOp.1
        by_cases hn8 : 8 ≤ n
        · exact (s168e3_false_of_omegaPlus_component_ge_eight c hcomp hn8 hOp).elim
        · obtain rfl : n = 6 := by omega
          exact (s168e3_false_of_sum_three_sl_four_of_r880 c h880 hcomp hsum htrans hs
            (s16low_isSLn_of_isAlt_eight (s15k_omp6_isAlt8 hOp))).elim
      · have hn4 : 4 ≤ n := s16k_four_le_of_isOmegaMinus hcomp.2.2 hOm
        obtain ⟨j, hj⟩ := hOm.1
        by_cases hn10 : 10 ≤ n
        · exact (s168e3_false_of_omegaMinus_component_ge_ten c hcomp hn10 hOm).elim
        · rcases (by omega : n = 4 ∨ n = 6 ∨ n = 8) with rfl | rfl | rfl
          · exact (hA5 (s16k_isAlt_five_of_isOmegaMinus_four hOm)).elim
          · exact (s168e3_false_of_sum_three_omega_minus_six c h869 hcomp hsum htrans hs
              hOm).elim
          · exact (s168e3_false_of_sum_three_omega_minus_eight c hcomp hsum htrans hs
              hOm).elim
      · have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hcomp.2.2 hA
        by_cases hn12 : 12 ≤ n
        · exact (s168e3_false_of_alternating_component_ge_twelve c hcomp hn12 hA).elim
        · interval_cases n
          · exact (hA5 hA).elim
          · exact s168e3_concl163F_of_sum_three_alt_six c h869 hcomp hsum htrans hs hA
          · exact s168e3_concl163F_of_sum_three_alt_seven c h880 hcomp hsum htrans hs hA
          · exact (s168e3_false_of_sum_three_sl_four_of_r880 c h880 hcomp hsum htrans hs
              (s16low_isSLn_of_isAlt_eight hA)).elim
          · exact (s168e3_false_of_sum_three_alt_nine c hcomp hsum htrans hs hA).elim
          · exact (s168e3_false_of_sum_three_alt_ten_eleven c hcomp hsum htrans hs
              (Or.inl rfl) hA h82).elim
          · exact (s168e3_false_of_sum_three_alt_ten_eleven c hcomp hsum htrans hs
              (Or.inr rfl) hA h82).elim
  ·
    rcases hirr with ⟨hirr_mem, -, -, h135⟩
    have hm3 := (s16k_mQuot_le_rk V₀ V hV
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) t).trans
      htrk
    exact s168e3_concl163F_of_nonthin_irreducible_of_s_eq_one c hcomp hs hodd hirr_mem _ rfl
      hm3 h135

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
