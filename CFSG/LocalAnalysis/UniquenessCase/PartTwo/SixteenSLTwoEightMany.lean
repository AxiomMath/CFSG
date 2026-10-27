module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCoverConjugateBounds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCTA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvdLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_case163_4_of_sl2_eight_of_one_lt_s
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : 1 < s15 D.M V₀ V hV L)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) :
    Case163_4 D V₀ V hV L := by
  obtain ⟨t, -, -, -, -, hW⟩ := c.conc
  have h3 : 3 ∣ Nat.card ↥(lBar V₀ V hV L) :=
    s16h_three_dvd_of_isSLn hcomp.2.2 hrow.1
  obtain ⟨K, hK, hbar⟩ :=
    s16h_exists_cover D c.std.h127 c.std.h119 c.setting.hyp151.hyp125 hcomp
  have hRkK : CFSG.Open.pRank 3 K = 1 :=
    s16h_pRank_three_eq_one_of_thin_cover D c.setting hcomp hW hthin h3 hK hbar
  have hle3 : s15 D.M V₀ V hV L ≤ 3 :=
    s168e3_s_le_three_of_pRank_one_cover c hK hbar hRkK
  have hs23 : s15 D.M V₀ V hV L = 2 ∨ s15 D.M V₀ V hV L = 3 := by omega
  have hL2 : UC22.IsL2 ↥(lBar V₀ V hV L) 3 :=
    CFSG.GroupTheory.isL2_of_isSLn_two (m := 3) (by norm_num) hrow.1
  obtain ⟨Kf, hKf, hKfin, hKcard, hR⟩ := hrow.2
  obtain ⟨-, -, -, hmap, -⟩ :=
    s168e3_section_kappa_data (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
  have hR' := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV)
    c (I := wTil V₀ V hV L) le_rfl hR
  rw [hmap] at hR'
  exact ⟨hL2, ⟨Kf, hKf, hKfin, hKcard, hR'⟩, hs23⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
