module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen3FCompNaturalOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLField48
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpOmegaField48
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSL3FourComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLThreeEightExclusion
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSUHighRankExclusion
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallClassicalRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallUnitarySolvable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSU4NaturalRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallClassicalDimensions
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenG2DerivedRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTripleA6Row
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenHatU43Row
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourExclusion
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeL5S1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeM22Exclusion
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeL34Exclusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

private theorem s16k_concl163F_of_field48_SL
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    {n m : ℕ} (hm : m = 2 ∨ m = 3)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n m) :
    Concl163F D V₀ V hV L := by
  have hn2 : 2 ≤ n := s16low_two_le_of_isSLn hcomp.2.2 hm hSL
  by_cases hn5 : 5 ≤ n
  · exact (s168e3_false_of_sl_component_field_four_eight_ge_five c hcomp hm hn5 hSL).elim
  · have hn4 : n ≤ 4 := by omega
    interval_cases n
    · obtain ⟨q, hq, hq2, hrank⟩ := hodd
      have hle := s16low_pRank_le_one_of_isSLn_two hm hSL hq hq2
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q)
        (lBar V₀ V hV L)] at hle
      omega
    · rcases hm with rfl | rfl
      · have h1 : s15 D.M V₀ V hV L = 1 :=
          s15_eq_one_of_sl3_four_component c hcomp hSL
        exact False.elim (by omega)
      · exact (s168e3_false_of_sl3Eight_component c hcomp hSL hs).elim
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s15_eq_one_of_sl_four_component_field_four_eight c hcomp hm hSL
      exact False.elim (by omega)

private theorem s16k_concl163F_of_field48_Sp
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    {n m : ℕ} (hm : m = 2 ∨ m = 3)
    (hSp : IsSpn ↥(lBar V₀ V hV L) n m) :
    Concl163F D V₀ V hV L := by
  have hn2 : 2 ≤ n := s16low_two_le_of_isSpn hcomp.2.2 hm hSp
  obtain ⟨k, hk⟩ := hSp.1
  by_cases hn8 : 8 ≤ n
  · exact (s168e3_false_of_sp_component_field_four_eight_ge_eight c hcomp hm hn8 hSp).elim
  · have hn : n = 2 ∨ n = 4 ∨ n = 6 := by omega
    rcases hn with rfl | rfl | rfl
    · obtain ⟨q, hq, hq2, hrank⟩ := hodd
      have hle := s16low_pRank_le_one_of_isSpn_two hm hSp hq hq2
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q)
        (lBar V₀ V hV L)] at hle
      omega
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s15_eq_one_of_sp_component_field_four_eight c hcomp hm (by norm_num) hSp
      exact False.elim (by omega)
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s15_eq_one_of_sp_component_field_four_eight c hcomp hm (by norm_num) hSp
      exact False.elim (by omega)

private theorem s16k_concl163F_of_field48_OmegaPlus
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    {n m : ℕ} (hm : m = 2 ∨ m = 3)
    (hOp : IsOmegaPlus ↥(lBar V₀ V hV L) n m) :
    Concl163F D V₀ V hV L := by
  have hn4 : 4 ≤ n := s16low_four_le_of_isOmegaPlus hcomp.2.2 hm hOp
  obtain ⟨k, hk⟩ := hOp.1
  by_cases hn8 : 8 ≤ n
  · exact (s168e3_false_of_omegaPlus_component_field_four_eight_ge_eight c hcomp hm hn8 hOp).elim
  · have hn : n = 4 ∨ n = 6 := by omega
    rcases hn with rfl | rfl
    · exact (C163.not_isQuasisimple_of_isOmegaPlus_four (by omega : 2 ≤ m) hOp
        hcomp.2.2).elim
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s15_eq_one_of_omegaPlus_component_field_four_eight c hcomp hm (by norm_num) hOp
      exact False.elim (by omega)

private theorem s16k_concl163F_of_field48_OmegaMinus
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    {n m : ℕ} (hm : m = 2 ∨ m = 3)
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) n m) :
    Concl163F D V₀ V hV L := by
  have hn4 : 4 ≤ n := s16low_four_le_of_isOmegaMinus hcomp.2.2 hm hOm
  obtain ⟨k, hk⟩ := hOm.1
  by_cases hn10 : 10 ≤ n
  · exact (s168e3_false_of_omegaMinus_component_field_four_eight_ge_ten c hcomp hm hn10 hOm).elim
  · have hn : n = 4 ∨ n = 6 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl
    · obtain ⟨q, hq, hq2, hrank⟩ := hodd
      have hle := s16low_pRank_le_one_of_isOmegaMinus_four hm hOm hq hq2
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q)
        (lBar V₀ V hV L)] at hle
      omega
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s15_eq_one_of_omegaMinus_component_field_four_eight c hcomp hm (by norm_num) hOm
      exact False.elim (by omega)
    · have h1 : s15 D.M V₀ V hV L = 1 :=
        s15_eq_one_of_omegaMinus_component_field_four_eight c hcomp hm (by norm_num) hOm
      exact False.elim (by omega)

theorem s16k_concl163F_of_irr_sameL
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    {t : MulAut (Vtil V₀ V hV)}
    (_ht : ⁅lBar V₀ V hV L, Subgroup.zpowers t⁆ = lBar V₀ V hV L)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (m : ℕ)
    (hm : m = E3.mQuot
      (commSub (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
          (Subgroup.zpowers t) ⊔
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
          fixV (lBar V₀ V hV L)))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hm3 : m ≤ 3)
    (h135 : Conc4_135 (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) m) :
    Concl163F D V₀ V hV L := by
  rcases h135 with
    ⟨n, hSL | hSp | hOp | hOm⟩ |
    ⟨n, hSL1 | hSp1 | hOp1 | hOm1 | hSU⟩ |
    hG2 | hTriple | hU43 | hAlt | hA7 |
    hSp6 | hL5 | hM22 | hL34 | hL32
  ·
    rcases hSL with ⟨hSL, hN⟩
    interval_cases m
    · obtain ⟨K, hF, hFin, hK, -⟩ := hSL
      exact ((Finite.one_lt_card (α := K)).ne' (by simpa using hK)).elim
    · exact s16nt_concl163F_of_binarySL_one c hcomp hs hodd hSL
        (by simpa [wTil, lBar] using hN)
    · exact s16k_concl163F_of_field48_SL c hcomp hs hodd (Or.inl rfl) hSL
    · exact s16k_concl163F_of_field48_SL c hcomp hs hodd (Or.inr rfl) hSL
  ·
    rcases hSp with ⟨hSp, hN⟩
    interval_cases m
    · obtain ⟨-, K, hF, hFin, hK, -⟩ := hSp
      exact ((Finite.one_lt_card (α := K)).ne' (by simpa using hK)).elim
    · exact s16nt_concl163F_of_binarySp_one c hcomp hs hSp
        (by simpa [wTil, lBar] using hN)
    · exact s16k_concl163F_of_field48_Sp c hcomp hs hodd (Or.inl rfl) hSp
    · exact s16k_concl163F_of_field48_Sp c hcomp hs hodd (Or.inr rfl) hSp
  ·
    rcases hOp with ⟨hOp, hN⟩
    interval_cases m
    · obtain ⟨-, K, hF, hFin, hK, -⟩ := hOp
      exact ((Finite.one_lt_card (α := K)).ne' (by simpa using hK)).elim
    · exact s16nt_concl163F_of_binaryOmegaPlus_one c hcomp hs hOp
    · exact s16k_concl163F_of_field48_OmegaPlus c hcomp hs (Or.inl rfl) hOp
    · exact s16k_concl163F_of_field48_OmegaPlus c hcomp hs (Or.inr rfl) hOp
  ·
    rcases hOm with ⟨hOm, hN⟩
    interval_cases m
    · obtain ⟨-, K, hF, hFin, b, c, hK, -⟩ := hOm
      exact ((Finite.one_lt_card (α := K)).ne' (by simpa using hK)).elim
    · exact s16nt_concl163F_of_binaryOmegaMinus_one c hcomp hs hodd hOm
    · exact s16k_concl163F_of_field48_OmegaMinus c hcomp hs hodd (Or.inl rfl) hOm
    · exact s16k_concl163F_of_field48_OmegaMinus c hcomp hs hodd (Or.inr rfl) hOm
  ·
    rcases hSL1 with ⟨hSL, hN⟩
    exact s16nt_concl163F_of_binarySL_one c hcomp hs hodd hSL
      (by simpa [wTil, lBar] using hN)
  ·
    rcases hSp1 with ⟨hSp, hN⟩
    exact s16nt_concl163F_of_binarySp_one c hcomp hs hSp
      (by simpa [wTil, lBar] using hN)
  ·
    rcases hOp1 with ⟨hOp, -⟩
    exact s16nt_concl163F_of_binaryOmegaPlus_one c hcomp hs hOp
  ·
    rcases hOm1 with ⟨hOm, -⟩
    exact s16nt_concl163F_of_binaryOmegaMinus_one c hcomp hs hodd hOm
  ·
    rcases hSU with ⟨hSU, hN⟩
    by_cases hn3 : n ≤ 3
    · have hsolv : Group.IsSolvable ↥(lBar V₀ V hV L) :=
        s16low_isSolvable_of_isSUn_le_three hn3 hSU
      have hcompA : CFSG.Assembly.IsComponentOf (lBar V₀ V hV L)
          (Mbar D.M V₀ V hV) :=
        CFSG.Assembly.isComponentOf_iff_open.mpr hcomp
      exact (CFSG.LocalAnalysis.ComponentInitial.not_le_of_isQuasisimple_of_isSolvable
        (K := lBar V₀ V hV L) (R := lBar V₀ V hV L)
        hcompA.2.2 hsolv le_rfl).elim
    · have hn4 : 4 ≤ n := by omega
      by_cases hn4eq : n = 4
      · subst hn4eq
        have h1 : s15 D.M V₀ V hV L = 1 :=
          s15_eq_one_of_su4_component_at_three c hcomp hSU
        exact False.elim (by omega)
      · have hn5 : 5 ≤ n := by omega
        exact (s168e3_false_of_su_component_ge_five c hcomp hn5 hSU).elim
  ·
    exact s168e3_concl163F_of_g2_component c hcomp hG2
  ·
    exact (s168e3_false_of_tripleA6_component c hcomp hirr hTriple).elim
  ·
    exact (s168e3_false_of_hat_u43_component c hcomp hU43.1).elim
  ·
    rcases hAlt with ⟨n, hA, hN⟩
    exact s16nt_concl163F_of_binaryAlt_one c h880 hcomp hs hodd hA
      (by simpa [wTil, lBar] using hN)
  ·
    exact s168e3_concl163F_of_a7Four_component c hcomp hA7
  ·
    have h1 : s15 D.M V₀ V hV L = 1 :=
      s15_eq_one_of_sp6_component_at_three c hcomp hSp6.1
    exact False.elim (by omega)
  ·
    exact (s168e3_l5_s1_false c (s15_eq_one_of_l5_component_at_three c hcomp hL5.1) hL5.1 hirr hL5.2).elim
  ·
    exact (s168e3_m22_false c hcomp hM22.1 hirr hM22.2).elim
  ·
    exact (s168e3_l34_false c hcomp hL34.1 hirr hL34.2).elim
  ·
    exact (not_s15ListTwo_of_odd_pRank hodd (Or.inl hL32.1)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
