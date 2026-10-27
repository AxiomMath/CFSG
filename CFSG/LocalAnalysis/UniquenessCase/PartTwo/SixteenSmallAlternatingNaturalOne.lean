module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalSmallRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltEightSLFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConvEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_concl163F_of_small_alternating_natural_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hN : AlternatingNatural (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) n) :
    Concl163F D V₀ V hV L := by
  obtain ⟨-, -, -, hmap, -⟩ := s168e3_section_kappa_data (D := D) (V₀ := V₀)
    (V := V) (L := L) (hV := hV) c
  have hNstar := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V)
    (L := L) (hV := hV) c (I := wTil V₀ V hV L) le_rfl hN
  rw [hmap] at hNstar
  have hn5 : 5 ≤ n := by
    rcases hn with rfl | rfl | rfl <;> norm_num
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn5, hA, hNstar⟩)))
  rcases hn with rfl | rfl | rfl
  · exact False.elim (s168e3_s15_ne_one_of_alt_six_seven c hperf (Or.inl hA) hs)
  · exact False.elim (s168e3_s15_ne_one_of_alt_six_seven c hperf (Or.inr hA) hs)
  ·
    have hSL4 : IsSLn ↥(lBar V₀ V hV L) 4 1 := s16low_isSLn_of_isAlt_eight hA
    have hLn4 : IsLn ↥(lBar V₀ V hV L) 4 1 := s16k_isLn_of_isSLn (by norm_num) hSL4
    have hL4 : s15ListFour ↥(lBar V₀ V hV L) := Or.inr (Or.inr (Or.inr hLn4))
    have h115 : F11.R115 D := uc22p22q_r115_of D c.std.hx c.std.h61
    have hsig : D.sig = {3} :=
      s15_Three_sig_three rAutRank153_holds rAbsIrr153_holds c.std.h127 h115
        c.std.h1217 c.setting.hyp151 hV c.ne hs hperf hL4 c.std.hx.sig_nonempty
        c.setting.hyp16.small
    have hA' : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨
        UC22.IsAlt ↥(lBar V₀ V hV L) 7 ∨ IsLn ↥(lBar V₀ V hV L) 4 1 :=
      Or.inr (Or.inr hLn4)
    have hO1 := s15_Three_O1a_of_alt rAutRank153_holds rAbsIrr153_holds rTable137_holds
      rTorus3_153_holds c.std.h127 h115 c.std.h1217 c.setting.hyp151 hV c.ne hs hperf hA'
      hsig c.setting.hyp16.small
    have h3 : 3 ∈ D.sig := by
      rw [hsig]
      exact Set.mem_singleton 3
    exact False.elim ((s15_Three_not_O1a_of_unique c.std.h61 c.std.h63 c.std.h127
      c.setting.hyp151.hyp125 (Or.inl h3)) hO1)

theorem s168e3_concl163F_of_omegaPlus_six_natural_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hOp : IsOmegaPlus ↥(lBar V₀ V hV L) 6 1)
    (hN : NatOmegaPlus (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 6 1) :
    Concl163F D V₀ V hV L :=
  s168e3_concl163F_of_small_alternating_natural_of_s_eq_one c hs (Or.inr (Or.inr rfl))
    (s15k_omp6_isAlt8 hOp) (s16k_alternatingNatural_eight_of_natOmegaPlus_six hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
