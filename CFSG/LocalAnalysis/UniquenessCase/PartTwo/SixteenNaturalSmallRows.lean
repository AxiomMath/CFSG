module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalComponentShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAutRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3List
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeC2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
  {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s168e3_s15Rs_self
    (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) :
    s15Rs D V₀ V hV L L = s15 D.M V₀ V hV L := by
  unfold s15Rs
  have hconj : conjSet (barSub V₀ V hV L) (s15NBar D V₀ V hV L) =
      {barSub V₀ V hV L} := by
    ext Z
    simp only [conjSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hninf : n ∈ Mbar D.M V₀ V hV ⊓
          normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set _) := by
        simpa only [s15NBar] using hn
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hninf.2
    · rintro rfl
      exact ⟨1, (s15NBar D V₀ V hV L).one_mem, by ext x; simp [Subgroup.mem_map]⟩
  rw [hconj, Set.ncard_singleton, one_mul]

theorem s168e3_s15_ne_one_of_listTwo
    (c : S168e3Ctx D V₀ V L hV)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) :
    s15 D.M V₀ V hV L ≠ 1 := by
  intro hs
  obtain ⟨p, hp⟩ := c.std.hx.sig_nonempty
  have hle := (s15_Three_rank_ListTwo rAutRank153_holds rAbsIrr153_holds D c.std.h1217
    c.setting.hyp151 hV c.ne hs hperf hL2).1 p (D.sig_prime p hp).1 (D.sig_prime p hp).2
  have h2 := c.two_le_pRank_mbar hp
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p)
    (H := Mbar D.M V₀ V hV)] at h2
  omega

theorem s168e3_s15_ne_one_of_alt_six_seven
    (c : S168e3Ctx D V₀ V L hV)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨
      UC22.IsAlt ↥(lBar V₀ V hV L) 7) :
    s15 D.M V₀ V hV L ≠ 1 := by
  intro hs
  have h115 : F11.R115 D := uc22p22q_r115_of D c.std.hx c.std.h61
  have hL4 : s15ListFour ↥(lBar V₀ V hV L) := by
    rcases hA with h6 | h7
    · exact Or.inr (Or.inl h6)
    · exact Or.inr (Or.inr (Or.inl h7))
  have hsig := s15_Three_sig_three rAutRank153_holds rAbsIrr153_holds c.std.h127 h115
    c.std.h1217 c.setting.hyp151 hV c.ne hs hperf hL4 c.std.hx.sig_nonempty
    c.setting.hyp16.small
  have hA' : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7 ∨
      IsLn ↥(lBar V₀ V hV L) 4 1 := by
    rcases hA with h6 | h7
    · exact Or.inl h6
    · exact Or.inr (Or.inl h7)
  have hO1 := s15_Three_O1a_of_alt rAutRank153_holds rAbsIrr153_holds rTable137_holds
    rTorus3_153_holds c.std.h127 h115 c.std.h1217 c.setting.hyp151 hV c.ne hs hperf hA' hsig
    c.setting.hyp16.small
  have h3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  exact (s15_Three_not_O1a_of_unique c.std.h61 c.std.h63 c.std.h127
    c.setting.hyp151.hyp125 (Or.inl h3)) hO1

theorem s168e3_unique_of_natPerf_of_two_le_s15
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hs : 2 ≤ s15 D.M V₀ V hV L) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M ∧ 3 ∉ D.sig := by
  have hshape := s168e3_shape_self_of_natPerf c hcomp hperf
  have hperf' : s15KNatPerf ↥(barSub V₀ V hV L)
      (barSub (v1Sub D.M V₀ V hV L) V hV L)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV L)) := by
    change s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L)
      (commSub ⊤ (lStar D.M V₀ V hV L))
    rw [s15_Three_commSub_top_lStar c.setting.hyp151 hV]
    exact hperf
  have hrs : s15Rs D V₀ V hV L L = s15 D.M V₀ V hV L := s168e3_s15Rs_self D V₀ V L hV
  have hnot : ¬ (s15Rs D V₀ V hV L L = 1 ∧ s15ExcList ↥(lBar V₀ V hV L)) := by
    rintro ⟨h1, -⟩
    rw [hrs] at h1
    omega
  have hO1 := s15_Three_O1a rTable137_holds rRank3List153_holds rAbsIrr153_holds
    rSimple153_holds c.std.h127 c.std.h119 c.std.h1217 c.setting.hyp151 hV c.ne hshape
    hperf' hnot
  exact s15_Three_unique_of_O1a c.std.h61 c.std.h63 c.std.h127
    c.setting.hyp151.hyp125 hO1

theorem s168e3_exists_cover_of_natPerf
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)) :
    ∃ Y : Subgroup G, s15Covers D V₀ V hV L Y := by
  have hshape := s168e3_shape_self_of_natPerf c hcomp hperf
  have hperf' : s15KNatPerf ↥(barSub V₀ V hV L)
      (barSub (v1Sub D.M V₀ V hV L) V hV L)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV L)) := by
    change s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L)
      (commSub ⊤ (lStar D.M V₀ V hV L))
    rw [s15_Three_commSub_top_lStar c.setting.hyp151 hV]
    exact hperf
  exact s15_Three_cover_K rSimple153_holds c.std.h127 c.std.h119 c.std.h1217
    c.setting.hyp151 hV hshape hperf'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
