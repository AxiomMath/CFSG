module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_case162_8_of_sl2_four_of_two_le_s
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : 2 ≤ s15 D.M V₀ V hV L)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 2) :
    Case162_8 D V₀ V hV L := by
  have hL2 : UC22.IsL2 ↥(lBar V₀ V hV L) 2 :=
    CFSG.GroupTheory.isL2_of_isSLn_two (m := 2) (by norm_num) hrow.1
  obtain ⟨K, hKf, hKfin, hKcard, hR⟩ := hrow.2
  obtain ⟨-, -, -, hmap, -⟩ :=
    s168e3_section_kappa_data (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
  have hR' := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV)
    c (I := wTil V₀ V hV L) le_rfl (by simpa [wTil, lBar] using hR)
  rw [hmap] at hR'
  exact ⟨Or.inl ⟨hL2, ⟨K, hKf, hKfin, hKcard, hR'⟩⟩, hs⟩

theorem s168e3_concl163F_of_sl2_four_of_two_le_s
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : 2 ≤ s15 D.M V₀ V hV L)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 2) :
    Concl163F D V₀ V hV L := by
  have h8 : Case162_8 D V₀ V hV L :=
    s168e3_case162_8_of_sl2_four_of_two_le_s c hs hrow
  refine Or.inl ?_
  refine Or.inr ?_
  refine Or.inr ?_
  refine Or.inr ?_
  refine Or.inr ?_
  refine Or.inr ?_
  refine Or.inr ?_
  refine Or.inr ?_
  refine Or.inr ?_
  exact Or.inl h8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
