module

public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions
public import CFSG.Yardstones.M3aba7dc4b8a8.TimmesfeldProvider
public import CFSG.Adapters.CatalogAgree
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2ExtraspecialWidthFour
public import CFSG.RankThree.GF2n.Statements
import CFSG.RankThree.GF2n.Assembly
import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover
import CFSG.GF2Type.Entry
import CFSG.GF2Type.ListIntro
import CFSG.GF2Type.ModelPSL
import CFSG.GF2Type.ModelPSU
import CFSG.LargeExtraspecial.S14C12RSHolds
public import CFSG.LargeExtraspecial.AS35WFinal
public import CFSG.LargeExtraspecial.AS35WRMain
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Yardstones.M3aba7dc4b8a8

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.Blueprint.NativeSporadic
  CFSG.LargeExtraspecial.Bridge CFSG.GF2Type CFSG.RankThree.GF2n
open scoped MatrixGroups

theorem gf2TypeList_of_aschbacher1976List {G : Type} [Group G] (h : Aschbacher1976List G) :
    GF2TypeList G := by
  unfold Aschbacher1976List at h
  rcases h with ⟨p, f, m, hp, hp2, hf, hm, hq, hmodel⟩ | (h | h | h) | h
  · exact gf2TypeList_of_psl_two hp hp2 hf hm hq hmodel
  · exact gf2TypeList_of_sporadic (s := .M11) (by simp) h
  · exact gf2TypeList_of_three (s := .PSL) (n := 3) (by simp) h
  · exact gf2TypeList_of_three (s := .PSU) (n := 3) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .HS) (by simp) h

theorem gf2TypeList_of_smith1979WidthFourList {G : Type} [Group G]
    (h : Smith1979WidthFourList G) : GF2TypeList G := by
  unfold Smith1979WidthFourList at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact gf2TypeList_of_psl (by norm_num) h
  · exact gf2TypeList_of_psu (by norm_num) h
  · exact gf2TypeList_of_omegaPlus (by norm_num) h
  · exact gf2TypeList_of_omegaMinus (by norm_num) h
  · exact gf2TypeList_of_exceptional (s := .trialityD4) (by simp) h
  · exact gf2TypeList_of_three (s := .POmegaPlus) (n := 4) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .Co2) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .Co1) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .Th) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .HN) (by simp) h

theorem gf2TypeList_of_smith1979WidthSixList {G : Type} [Group G]
    (h : Smith1979WidthSixList G) : GF2TypeList G := by
  unfold Smith1979WidthSixList at h
  rcases h with h | h | h | h | h | h
  · exact gf2TypeList_of_psl (by norm_num) h
  · exact gf2TypeList_of_psu (by norm_num) h
  · exact gf2TypeList_of_omegaPlus (by norm_num) h
  · exact gf2TypeList_of_omegaMinus (by norm_num) h
  · exact gf2TypeList_of_sporadic (s := .J4) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .Fi24Prime) (by simp) h

section TwistedE6

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14

theorem reifartSmithU62Input_of_gh74 (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) :
    CFSG.LargeExtraspecial.S14.ReifartSmithU62Input :=
  CFSG.LargeExtraspecial.S14.reifartSmithU62Input_of_widthTwo
    (aschbacherWidthTwoResidual_of_gh74 hgh AS35W.rankTwoW2Input)

end TwistedE6

section Reduction

theorem lc_gl_gf2_recognition_rank_four_of_yardstones_legacy
    (h01 : Aschbacher1976CenterFourCase) (h02 : Aschbacher1976HigherCenterCase)
    (h03 : WidthFourWeaklyClosedCase) (h04 : WidthFourReducibleCase)
    (h05 : WidthFourIrreducibleCase) (h06 : WidthSixAlternativeFourCase)
    (h07 : OrthogonalCase) (h08 : WidthTenE6Case) (h09 : WidthsSixteenTwentyEightCase)
    (h10 : WidthElevenCo2Case) (h11 : WidthTwelveCo1Case) (hT : MainStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G) (he : 4 ≤ CFSG.Assembly.evenRank G)
    (hgf2 : CFSG.Assembly.LargeEvenGF2Type G) : CFSG.Assembly.InCatalog G := by
  suffices hlist : GF2TypeList G from
    QTFaithfulEmptyTauCeti.inCatalog_of_catalog G (catalog_of_gf2TypeList hlist)
  obtain ⟨M, hMmax, hsymp, B, hB, hBM⟩ := hgf2
  have hchar' : IsCharacteristicPType G 2 := CFSG.GH74.isCharTwoType_iff.mp hchar
  have he' : 4 ≤ twoLocalOddRank G := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]
    exact he
  obtain ⟨⟨z, -, hz2, -, hMz, -⟩, hFQ, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_witness_centralizer_and_rank (G := G) hchar'
      (M := M) (B := B) hMmax hsymp hB hBM (Q := inSubgroup (CFSG.pCore 2) M) rfl
      (r := GLATwoLocalRank 3 G) rfl
  subst hMz
  have hset : GF2RankFourSetting G z := ⟨hnonab, hK, hchar, he, hz2, hMmax, hsymp, B, hB, hBM⟩
  have hloc : IsPLocal 2 (Subgroup.centralizer ({z} : Set G)) := by
    obtain ⟨P, hP1, hP2, hMP⟩ := hMmax.1
    exact ⟨P, hP1, hP2, hMP⟩
  by_cases hext : IsExtraspecialPGroup 2 (coreQ z)
  swap
  · by_cases hexp : ∀ x ∈ coreQ z, x ^ 4 = 1
    · exact gf2TypeList_of_aschbacher1976List (h01 G z hset hext hexp)
    · have hexp' : ∃ x ∈ coreQ z, x ^ 4 ≠ 1 := by
        by_contra hcon
        exact hexp fun x hx => by_contra fun h4 => hcon ⟨x, hx, h4⟩
      exact gf2TypeList_of_aschbacher1976List (h02 G z hset hext hexp')
  obtain ⟨w, hw4, hcard, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_extraspecial_width_at_least_four_at_rank_four
      (G := G) hchar' he' (M := Subgroup.centralizer ({z} : Set G)) (B := B) hMmax hsymp hB hBM
      (Q := coreQ z) hFQ hext (r := GLATwoLocalRank 3 G) rfl
  rcases Nat.lt_or_ge w 5 with hw | hw5
  ·
    obtain rfl : w = 4 := by omega
    have hcard9 : Nat.card (coreQ z) = 2 ^ 9 := by rw [hcard]
    by_cases hwc : ZWeaklyClosedInCore z
    · rcases h03 G z hset hext hcard9 hwc with h | h
      · exact gf2TypeList_of_psu (by norm_num) h
      · exact gf2TypeList_of_sporadic (s := .Co2) (by simp) h
    by_cases hred : CoreReducible z
    · exact gf2TypeList_of_psl (by norm_num) (h04 G z hset hext hcard9 hwc hred)
    exact gf2TypeList_of_smith1979WidthFourList (h05 G z hset hext hcard9 hwc hred)
  obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hcard
  obtain ⟨Mbar, _, hMbar⟩ :=
    exists_quotient_generalizedFitting ↥(Subgroup.centralizer ({z} : Set G))
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  rcases hT G hnonab z hz2 hext' w hcard' Mbar hMbar' with
    h | (⟨⟨e⟩⟩ | ⟨⟨e⟩⟩) | ⟨h6w, hev, q, hq, hqM⟩ | h4 | ⟨rfl, -, hFS⟩ | ⟨rfl, hCo2⟩ |
      ⟨rfl, hCo1⟩ | ⟨hsimp, t, ht, htext, hcases⟩
  ·
    omega
  ·
    exact gf2TypeList_of_psl (by omega) (lieModel_psl_two_of_mulEquiv (by omega) e)
  ·
    exact gf2TypeList_of_psu (by omega) (lieModel_psu_two_of_mulEquiv (by omega) e)
  ·
    obtain ⟨hplus, hminus⟩ := h07 G z hset hext w hcard h6w hev Mbar hMbar q hq hqM
    by_cases hp : timmesfeldPlusType q
    · exact gf2TypeList_of_omegaPlus (by omega) (hplus hp)
    · exact gf2TypeList_of_omegaMinus (by omega) (hminus hp)
  ·
    obtain rfl : w = 6 := h4.1
    exact gf2TypeList_of_smith1979WidthSixList
      (h06 G z hset hext (by rw [hcard]) Mbar hMbar h4)
  ·
    rcases hFS with h | h
    · exact gf2TypeList_of_exceptional (s := .E6) (by simp)
        ((h08 G z hset hext (by rw [hcard]) Mbar hMbar).1 h)
    · exact gf2TypeList_of_exceptional (s := .twistedE6) (by simp)
        ((h08 G z hset hext (by rw [hcard]) Mbar hMbar).2 h)
  ·
    obtain ⟨hB, d₀, hd₀, hrank, d, hd, hc⟩ :=
      h10 G z hset hext (by rw [hcard]) Mbar hMbar hCo2
    exact gf2TypeList_of_sporadic (s := .B) (by simp)
      hB
  ·
    obtain ⟨hMonster, d₀, hd₀, hrank, a, ha⟩ :=
      h11 G z hset hext (by rw [hcard]) Mbar hMbar hCo1
    exact gf2TypeList_of_sporadic (s := .M) (by simp)
      hMonster
  ·
    obtain ⟨h16, h28⟩ := h09 G z hset hext w hcard Mbar hMbar hsimp t ht htext
    rcases hcases with ⟨hw, hc, hqu⟩ | ⟨hw, hc, hqu⟩
    · exact gf2TypeList_of_exceptional (s := .E7) (by simp) (h16 hw hc hqu)
    · exact gf2TypeList_of_exceptional (s := .E8) (by simp) (h28 hw hc hqu)
theorem gf2_recognition_rank_four_of_yardstones
    (h01 : Aschbacher1976CenterFourCase) (h02 : Aschbacher1976HigherCenterCase)
    (h03 : WidthFourWeaklyClosedCase) (h04 : WidthFourReducibleCase)
    (h05 : WidthFourIrreducibleCase) (h06 : WidthSixAlternativeFourCase)
    (h07 : OrthogonalCase) (h08 : WidthTenE6Case) (h09 : WidthsSixteenTwentyEightCase)
    (h10 : WidthElevenCo2Case) (h11 : WidthTwelveCo1Case) (hT : TimmesfeldPrintedStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G) (he : 4 ≤ CFSG.Assembly.evenRank G)
    (hgf2 : CFSG.Assembly.LargeEvenGF2Type G) : CFSG.Assembly.InCatalog G :=
  lc_gl_gf2_recognition_rank_four_of_yardstones_legacy h01 h02 h03 h04 h05 h06 h07 h08 h09 h10
    h11 (timmesfeldMainStatement_of_printedStatement hT) G hnonab hK hchar he hgf2

end Reduction

end CFSG.Yardstones.M3aba7dc4b8a8
