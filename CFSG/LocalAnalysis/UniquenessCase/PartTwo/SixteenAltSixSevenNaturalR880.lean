module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalSmallRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKIso
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNotJ2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalShapeL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltSevenVector
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallRowsB7
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallCount
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Engine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem isStronglyPEmbedded_three_of_r880
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) (h127 : R127 D) (h119 : F11.R119 D)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7 ∨
      IsLn ↥(lBar V₀ V hV L) 4 1 ∨ IsLn ↥(lBar V₀ V hV L) 5 1) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) := by
    rcases hA with h6 | h7 | h4 | h5
    · exact s16c167_cfg2_simple_alt (by norm_num) h6
    · exact s16c167_cfg2_simple_alt (by norm_num) h7
    · exact s16c167_cfg2_simple_ln h4
    · exact s16c167_cfg2_simple_ln h5
  obtain ⟨K, hK, hbar, hiso⟩ :=
    exists_calC_cover_of_simple_component h125 h127 h119 hcomp hsimple
  have hcover : s15Covers D V₀ V hV L K := by
    change K ∈ calC D.M ∧ ∃ m ∈ D.M,
      barSub V₀ V hV K = barSub V₀ V hV (conjSubgroup L m) ∧
        Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* ↥(barSub V₀ V hV L))
    refine ⟨hK, 1, D.M.one_mem, ?_, hiso⟩
    rw [conjSubgroup_one]
    exact hbar
  have hA' : UC22.IsAlt ↥(barSub V₀ V hV L) 6 ∨
      UC22.IsAlt ↥(barSub V₀ V hV L) 7 ∨
      IsLn ↥(barSub V₀ V hV L) 4 1 ∨ IsLn ↥(barSub V₀ V hV L) 5 1 := hA
  exact s15_Three_strong_alt h880 rSchur153_holds rIso153_holds rNotJ2_holds hcover hA'

theorem s168e3_false_of_alt_six_seven_natural_of_r880
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hNat : AlternatingNatural (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) n) : False := by
  obtain ⟨-, -, -, hmap, -⟩ := s168e3_section_kappa_data (D := D) (V₀ := V₀)
    (V := V) (L := L) (hV := hV) c
  have hNatStar := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V)
    (L := L) (hV := hV) c (I := wTil V₀ V hV L) le_rfl hNat
  rw [hmap] at hNatStar
  have hn5 : 5 ≤ n := by
    rcases hn with h6 | h7
    · omega
    · omega
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn5, hA, hNatStar⟩)))
  have hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    (s168e3_unique_of_natPerf_of_two_le_s15 c hcomp hperf (by omega)).1
  obtain ⟨Y, hY⟩ := s168e3_exists_cover_of_natPerf c hcomp hperf
  have hA' : UC22.IsAlt ↥(barSub V₀ V hV L) 6 ∨
      UC22.IsAlt ↥(barSub V₀ V hV L) 7 ∨
      IsLn ↥(barSub V₀ V hV L) 4 1 ∨ IsLn ↥(barSub V₀ V hV L) 5 1 := by
    rcases hn with rfl | rfl
    · refine Or.inl ?_
      change UC22.IsAlt ↥(lBar V₀ V hV L) 6
      exact hA
    · refine Or.inr (Or.inl ?_)
      change UC22.IsAlt ↥(lBar V₀ V hV L) 7
      exact hA
  exact hnotStrong (s15_Three_strong_alt (D := D) (V₀ := V₀) (V := V)
    (K₀ := L) (hV := hV) h880 rSchur153_holds rIso153_holds rNotJ2_holds hY hA')

theorem s168e3_concl163F_of_alt_six_seven_natural_of_r880
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hNat : AlternatingNatural (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) n) :
    Concl163F D V₀ V hV L :=
  False.elim (s168e3_false_of_alt_six_seven_natural_of_r880 c h880 hcomp hs hn hA hNat)

theorem s168e3_false_of_sum_three_alt_seven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h880 : F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hA7 : UC22.IsAlt ↥(lBar V₀ V hV L) 7) : False := by
  have hT := s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have h7 := s168e3_irrSet_seven_of_bounded c hcomp hsum htrans hs
    ⟨7, Or.inr (Or.inr (Or.inr (Or.inr ⟨hA7, by norm_num⟩)))⟩
  have hm := mBarGT_two_of_threeNat c.setting hT
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    isStronglyPEmbedded_three_of_r880 c.setting.hyp16.hyp125 c.std.h127 c.std.h119
      h880 hcomp (Or.inr (Or.inl hA7))
  have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hsp
  have hOp : F10.OpRes 3 D.M = D.M :=
    c.std.h638 3 Nat.prime_three (by norm_num) (Or.inr hsp)

  have hgood : V₀ = ⊥ →
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧
        Subgroup.centralizer ({v} : Set G) ≤ D.M := by
    intro hV₀
    have hcard : Nat.card ↥(lBar V₀ V hV L) = 2520 := by
      rw [s15k_six_alt_card hA7 (by norm_num : 2 ≤ 7)]
      norm_num [Nat.factorial]
    have htag := SumOfNatShape.alt_seven_of_card_eq_2520 hcomp.2.2 hcard hsum
    have hD7 : SumOfNat (fun H U Z => AlternatingNatural H U Z 7)
        (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3 := by
      simpa only [wTil, lBar] using htag.2
    obtain ⟨w, hw, hwT, E, hEH, hE3, hEnc, hEw⟩ :=
      hT.exists_fixed_vector_alt_seven hA7 hD7
    obtain ⟨v, hvV, _hv1, hvT, hvC⟩ :=
      Setting16.good_vector_of_fix_of_stronglyEmbedded (V₀ := V₀) (V := V)
        (L := L) (hV := hV) c.setting c.std.h61 c.std.h63 hsp hV₀ hw
        (fun t => mem_fixV.mp hwT (t : MulAut _) t.2)
        (hEH.trans hT.le) hE3 hEnc hEw
    exact ⟨v, hvV, hvT, hvC⟩

  obtain ⟨_N, _hNM, _hLN, _hNfix, _hcomm, _hdisj, _hsup, hK⟩ :=
    hT.structure_of_seven h7
  rcases hK with hK7 | hK21 | ⟨hK168, _hKsimple⟩
  · obtain ⟨Y, hYM, hY3, hYexp, hYnc, hperm, _h9⟩ :=
      s168e3_exists_permuting_three_alt_seven_k7 c hT h7 hA7 hK7
    refine false_of_permuting_three_of_stronglyEmbedded D c.std.hx c.std.h61
      c.std.h63 c.std.h126 c.std.h1211 c.std.h111 c.std.h6161ii hsp
      (V₀ := V₀) (V := V) (L := L) c.setting hm hYM hY3 hYexp
      hYnc hperm ?_
    by_cases hV₀ : V₀ = ⊥
    · exact Or.inr (Or.inr (hgood hV₀))
    · exact Or.inl hV₀
  · exact c.setting.false_of_kBar_order_21_of_opRes hOp hT h7 hK21
  · obtain ⟨Y, hYM, hY3, hYexp, hYnc, hperm, hbig⟩ :=
      s168e3_exists_permuting_three_alt_seven_k168 c hT h7 hA7 hK168
    exact false_of_permuting_three_big_of_stronglyEmbedded
      D c.std.h63 c.std.h126 c.std.h1211 c.std.h111 c.std.h6161ii
      hk hsp c.setting hm hYM hY3 hYexp hYnc hperm (Or.inr hbig)

theorem s168e3_concl163F_of_sum_three_alt_seven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h880 : F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hA7 : UC22.IsAlt ↥(lBar V₀ V hV L) 7) :
    Concl163F D V₀ V hV L :=
  False.elim (s168e3_false_of_sum_three_alt_seven c h880 hcomp hsum htrans hs hA7)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
