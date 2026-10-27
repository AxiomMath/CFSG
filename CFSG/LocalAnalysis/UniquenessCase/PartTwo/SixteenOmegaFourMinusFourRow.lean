module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaFourMinusOneExclusion
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_case162_8_of_omegaMinus_four_four_of_two_le_s
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : 2 ≤ s15 D.M V₀ V hV L)
    (hrow : s16h_H5RowO4 (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 2) :
    Case162_8 D V₀ V hV L := by
  obtain ⟨hOm, hNat⟩ := hrow
  obtain ⟨hEven, K, hKf, hKfin, b₀, c₀, hKcard, hdisc, hR⟩ := hNat
  obtain ⟨-, -, -, hmap, -⟩ :=
    s168e3_section_kappa_data (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
  have hR' := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V) (L := L)
    (hV := hV) c (I := wTil V₀ V hV L) le_rfl (by simpa [wTil, lBar] using hR)
  rw [hmap] at hR'
  exact ⟨Or.inr ⟨hOm, hEven, K, hKf, hKfin, b₀, c₀, hKcard, hdisc, hR'⟩, hs⟩

theorem s168e3_case162_8_of_omegaMinus_four_four
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hrow : s16h_H5RowO4 (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 2) :
    Case162_8 D V₀ V hV L := by
  have hs1 : 1 ≤ s15 D.M V₀ V hV L := Om8Excl.one_le_s15 D.M V₀ V hV L
  have hs2 : 2 ≤ s15 D.M V₀ V hV L := by
    by_contra h
    have hs : s15 D.M V₀ V hV L = 1 := by omega
    exact s168e3_false_of_omegaMinus_four_of_s_eq_one c hcomp hthin hs (Or.inl rfl) hrow
  exact s168e3_case162_8_of_omegaMinus_four_four_of_two_le_s c hs2 hrow

theorem s168e3_concl163F_of_omegaMinus_four_four
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hrow : s16h_H5RowO4 (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 2) :
    Concl163F D V₀ V hV L := by
  have h8 : Case162_8 D V₀ V hV L :=
    s168e3_case162_8_of_omegaMinus_four_four c hcomp hthin hrow
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
