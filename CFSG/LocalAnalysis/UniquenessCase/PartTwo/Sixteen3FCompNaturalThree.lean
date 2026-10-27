module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenListTwoOddRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltEightSLFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSp6Row
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeAlternatingComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeClassicalComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneS1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLFourComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLSixSevenComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeL5Conjugates
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem s168e3_concl163F_of_sumOfNatShape_three_of_alt67_three
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓
        normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hAlt3 :
      ∀ {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
        (_c : S168e3Ctx D V₀ V L hV)
        (_hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
        (_hs : s15 D.M V₀ V hV L = 2)
        {n : ℕ} (_hn : n = 6 ∨ n = 7)
        (_hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
        (_hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
          (lBar V₀ V hV L) (wTil V₀ V hV L)
          (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
        (_htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
          ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
          ∃ g ∈ Mbar D.M V₀ V hV ⊓
            normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
            I₂ = I₁.map g.toMonoidHom),
        Concl163F D V₀ V hV L) :
    Concl163F D V₀ V hV L := by
  have hs : 1 < s15 D.M V₀ V hV L := by omega
  rcases hsum with ⟨n, hSL | hSp | hOp | hOm | hAlt⟩
  ·
    rcases hSL with ⟨hSL, -⟩
    have hn3 : 3 ≤ n := s16k_three_le_of_isSLn hcomp.2.2 hSL
    by_cases hn8 : 8 ≤ n
    · exact (s168e3_false_of_sl_component_ge_eight c hcomp hn8 hSL).elim
    · have hn7 : n ≤ 7 := by omega
      interval_cases n
      · have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := by
          simpa [IsL3, IsLn] using s16k_isLn_of_isSLn (by norm_num) hSL
        exact (not_s15ListTwo_of_odd_pRank hodd (Or.inl hL3)).elim
      · have h1 : s15 D.M V₀ V hV L = 1 :=
          s15_eq_one_of_sl_four_component_at_three c hcomp hSL
        exact False.elim (by omega)
      · have hLn : IsLn ↥(lBar V₀ V hV L) 5 1 :=
          s16k_isLn_of_isSLn (by norm_num) hSL
        have h1 : s15 D.M V₀ V hV L = 1 :=
          s15_eq_one_of_l5_component_at_three c hcomp hLn
        exact False.elim (by omega)
      · have h1 : s15 D.M V₀ V hV L = 1 :=
          s15_eq_one_of_sl_six_seven_component_at_three c hcomp
            (Or.inl rfl) hSL
        exact False.elim (by omega)
      · have h1 : s15 D.M V₀ V hV L = 1 :=
          s15_eq_one_of_sl_six_seven_component_at_three c hcomp
            (Or.inr rfl) hSL
        exact False.elim (by omega)
  ·
    rcases hSp with ⟨hSp, -⟩
    have hn6 : 6 ≤ n := s16k_six_le_of_isSpn hcomp.2.2 hSp
    obtain ⟨k, hk⟩ := hSp.1
    by_cases hn8 : 8 ≤ n
    · exact (s168e3_false_of_sp_component_ge_eight c hcomp hn8 hSp).elim
    · have hn : n = 6 := by omega
      subst hn
      have h1 : s15 D.M V₀ V hV L = 1 :=
        s15_eq_one_of_sp6_component_at_three c hcomp hSp
      exact False.elim (by omega)
  ·
    rcases hOp with ⟨hOp, -⟩
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
  ·
    rcases hOm with ⟨hOm, -⟩
    have hn4 : 4 ≤ n := s16k_four_le_of_isOmegaMinus hcomp.2.2 hOm
    obtain ⟨k, hk⟩ := hOm.1
    by_cases hn10 : 10 ≤ n
    · exact (s168e3_false_of_omegaMinus_component_ge_ten c hcomp hn10 hOm).elim
    · have hn : n = 4 ∨ n = 6 ∨ n = 8 := by omega
      rcases hn with rfl | rfl | rfl
      · have hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5 :=
          s16k_isAlt_five_of_isOmegaMinus_four hOm
        exact (not_s15ListTwo_of_odd_pRank hodd (Or.inr hA5)).elim
      · have h1 : s15 D.M V₀ V hV L = 1 :=
          s15_eq_one_of_omega_minus_six_component c hcomp hOm
        exact False.elim (by omega)
      · have h1 : s15 D.M V₀ V hV L = 1 :=
          s16nt_s15_eq_one_of_omega_minus_eight c hcomp hOm
        exact False.elim (by omega)
  ·
    rcases hAlt with ⟨hA, hSum⟩
    have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hcomp.2.2 hA
    by_cases hn12 : 12 ≤ n
    · exact (s168e3_false_of_alternating_component_ge_twelve c hcomp hn12 hA).elim
    · have hn11 : n ≤ 11 := by omega
      interval_cases n
      · exact (not_s15ListTwo_of_odd_pRank hodd (Or.inr hA)).elim
      · exact hAlt3 c hcomp hs2 (Or.inl rfl) hA
          (by simpa [wTil, lBar] using hSum) htrans
      · exact hAlt3 c hcomp hs2 (Or.inr rfl) hA
          (by simpa [wTil, lBar] using hSum) htrans
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

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
