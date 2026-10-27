module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLFourComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeC2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAutRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_concl163F_of_naturalSL_four
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSL4 : IsSLn ↥(lBar V₀ V hV L) 4 1)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 4 1) :
    Concl163F D V₀ V hV L := by
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_sl_four_component_at_three c hcomp hSL4
  have hLn4 : IsLn ↥(lBar V₀ V hV L) 4 1 := s16k_isLn_of_isSLn (by norm_num) hSL4
  obtain ⟨-, θ, -, hmap, -⟩ :=
    s168e3_section_kappa_data (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
  obtain ⟨K, hKf, hKfin, hKcard, hR⟩ := hN
  have hR' := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
    (I := wTil V₀ V hV L) le_rfl hR
  rw [hmap] at hR'
  have hNstar : BinaryNaturalSL (lStar D.M V₀ V hV L)
      (wStar D.M V₀ V hV L) ⊥ 4 1 :=
    ⟨K, hKf, hKfin, hKcard, hR'⟩
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inl ⟨4, by norm_num, hLn4, hNstar⟩
  have hL4 : s15ListFour ↥(lBar V₀ V hV L) := Or.inr (Or.inr (Or.inr hLn4))
  have hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7 ∨
      IsLn ↥(lBar V₀ V hV L) 4 1 := Or.inr (Or.inr hLn4)
  have h115 := uc22p22q_r115_of D c.std.hx c.std.h61
  have hsig := s15_Three_sig_three rAutRank153_holds rAbsIrr153_holds
    c.std.h127 h115 c.std.h1217 c.setting.hyp151 hV c.ne hs hperf hL4
    c.std.hx.sig_nonempty c.setting.hyp16.small
  have hO1 := s15_Three_O1a_of_alt rAutRank153_holds rAbsIrr153_holds
    rTable137_holds rTorus3_153_holds c.std.h127 h115 c.std.h1217
    c.setting.hyp151 hV c.ne hs hperf hA hsig c.setting.hyp16.small
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  exact False.elim ((s15_Three_not_O1a_of_unique
    c.std.h61 c.std.h63 c.std.h127 c.setting.hyp151.hyp125 (Or.inl h3)) hO1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
