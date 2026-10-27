module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviFoldCells
public import CFSG.LocalAnalysis.StandardType.GGTBJE6Rows
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJTwE6LeviL_three_of
    (hC : GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 2 ≤ n))
    (hC1 : GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1)) :
    GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ p ≠ 3 := by
  intro G _ _ p B Bs x L D J y K hH hFact hinn hX n hΛ hL hreg labJ hΛJ hJlab hdvd hnc
  have hp3 : p = 3 := by
    by_contra h
    exact hnc (Or.inr h)
  have hn1 : 1 ≤ n := hΛ.1
  by_cases hn2 : 2 ≤ n
  · exact hC G p B Bs x L D J y K hH hinn hX n hΛ hL hreg labJ hΛJ hJlab hdvd
      (fun h => h.elim (fun h' => hnc (Or.inl h')) fun h' => h' ⟨hp3, hn2⟩)
  · exact hC1 G p B Bs x L D J y K hH hinn hX n hΛ hL hreg labJ hΛJ hJlab hdvd
      (fun h => h.elim (fun h' => hnc (Or.inl h')) fun h' => h' ⟨hp3, by omega⟩)

theorem ggTBJTwE6LeviK_three_of
    (hRig : GGLabelRigidInput)
    (hC : GGTBJETypeLeviK .twE6 fun p n labJ =>
      ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 2 ≤ n ∧ 3 ∣ 2 ^ n + 1))
    (hC1 : GGTBJETypeLeviK .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1)) :
    GGTBJETypeLeviK .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ p ≠ 3 := by
  intro G _ _ p B Bs x L D J y K hH hJK hFact hinn hX n hΛ hK hreg labJ hΛJ hJlab hdvd hnc
  have hp3 : p = 3 := by
    by_contra h
    exact hnc (Or.inr h)
  have hn1 : 1 ≤ n := hΛ.1
  by_cases hn2 : 2 ≤ n
  · by_cases h3 : 3 ∣ 2 ^ n + 1
    · exact hC G p B Bs x L D J y K hH hJK hinn hX n hΛ hK hreg labJ hΛJ hJlab hdvd
        (fun h => h.elim (fun h' => hnc (Or.inl h')) fun h' => h' ⟨hp3, hn2, h3⟩)
    · have hm : 3 ∣ 2 ^ n - 1 := by
        rcases id hreg with h | h
        · rw [hp3] at h
          exact h
        · rw [hp3] at h
          exact absurd h h3
      exact ggTBJTwE6LeviK_foldThree hRig G p B Bs x L D J y K hH hJK hinn hX n hΛ hK hreg labJ
        hΛJ hJlab hdvd (fun h => h.elim (fun h' => hnc (Or.inl h')) fun h' => h' ⟨hp3, hm⟩)
  · exact hC1 G p B Bs x L D J y K hH hJK hinn hX n hΛ hK hreg labJ hΛJ hJlab hdvd
      (fun h => h.elim (fun h' => hnc (Or.inl h')) fun h' => h' ⟨hp3, by omega⟩)

theorem ggTBJLeftOnLab_twE6_three
    (hcell : GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ p ≠ 3) :
    GGTBJLeftOnLab ggTBJTwE6LabelThree := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨⟨ht, hphi⟩, hp3⟩ := hS
  have ht' : t = .twE6 := ht
  subst ht'
  have hr : r = 0 := hΛ.2
  subst hr
  have hreg := ggLabPhiOneTwo_dvd hp.out hphi
  have hL' : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1.1, hP.2⟩) hL
  by_cases hc : ggTBJTwE6RowCand p n labJ
  · exact Or.inr (Or.inr (ggTBJTwE6RowL_holds G p B Bs x L D J y K hH hL' hX n hΛ hhas hreg labJ
      hΛJ hhasJ hdvd hc))
  · exact (hcell G p B Bs x L D J y K hH hL' hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd
      fun h => h.elim hc fun h' => h' hp3).imp id Or.inl

theorem ggTBJNbrOnLab_twE6_three
    (hI3 : GGNbrSubcomponentInput)
    (hcell : GGTBJETypeLeviK .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ p ≠ 3) :
    GGTBJNbrOnLab ggTBJTwE6LabelThree := by
  intro G _ _ p B Bs x L D J y K hH hp hK hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨⟨ht, hphi⟩, hp3⟩ := hS
  have ht' : t = .twE6 := ht
  subst ht'
  have hr : r = 0 := hΛ.2
  subst hr
  have hreg := ggLabPhiOneTwo_dvd hp.out hphi
  have hK' : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1.1, hP.2⟩) hK
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hH.2.2.2.2.1
  by_cases hc : ggTBJTwE6RowCand p n labJ
  · exact Or.inr (Or.inr (ggTBJTwE6RowK_holds G p B Bs x L D J y K hH hJK hK' hX n hΛ hhas hreg
      labJ hΛJ hhasJ hdvd hc))
  · exact (hcell G p B Bs x L D J y K hH hJK hK' hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd
      fun h => h.elim hc fun h' => h' hp3).imp id Or.inl

theorem GGTBJOrdinaryOutside.of_twE6_three
    {E : ℕ → LargeEvenLabel → Prop}
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    (hL : GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ p ≠ 3)
    (hK : GGTBJETypeLeviK .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ p ≠ 3)
    (h : GGTBJOrdinaryOutside fun p lab => E p lab ∨ ggTBJTwE6LabelThree p lab) :
    GGTBJOrdinaryOutside E :=
  GGTBJOrdinaryOutside.of_proved ((ggTBJLeftOnLab_twE6_three hL).toLeftOn hTCJ)
    ((ggTBJNbrOnLab_twE6_three hI3 hK).toNbrOn hTCJ hI3) h

end CFSG.StandardType

end
