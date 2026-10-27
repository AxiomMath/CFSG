module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.JMFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.BorelTits (orthGroup)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof (IsChar2LieShape)
open CFSG.ComponentClassification.CatLeafProof
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem isSimpleGroup_bar2_of_hyp18 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hXL : conjClosure D.M L = L) : IsSimpleGroup (Bar2 L) := by
  have hXc : L ∈ S17.calLjStar D p (S17.jM D p) := by
    have h0 := (S17.mem_calL0Star (D := D) (p := p)).1 h.hX
    rwa [hXL] at h0
  simp only [S17.calLjStar] at hXc
  split_ifs at hXc with hj1 hj2 hj3 hj4 hj5
  · rw [S17.mem_calL1Star] at hXc
    rcases hXc.2 with ⟨f, hg2 | hsp | hu4⟩ | hu5
    · exact (CFSG.LieType.Simplicity.fam_g2_simplicity (Bar2 L) 2 f
        (LieModel.chevalleyExceptionalModel hg2 (by decide))).2
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hu4
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hu5
  · rw [S17.mem_calL2Star] at hXc
    exact absurd h.hL hXc.2.1
  · rw [S17.mem_calL3Star] at hXc
    exact absurd h.hL.1.2.2 (S17.not_isQuasisimple_of_isA5xA5 hXc.2)
  · rw [S17.mem_calL4Star] at hXc
    rcases hXc.2.1 with ⟨n, hl2 | hu3⟩
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hl2
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hu3
  · rw [S17.mem_calL5Star] at hXc
    obtain ⟨e⟩ := hXc.2
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    exact MulEquiv.isSimpleGroup e
  · exact absurd hXc (by simp)

theorem conjClosure_eq_and_bar2_equiv_of_hyp18 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (hs : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) :
    conjClosure D.M L = L ∧
      Nonempty (Bar2 L ≃* ↥(barSub V₀ V h.hyp125.isElemAbelian L)) := by
  have hXL : conjClosure D.M L = L :=
    conjClosure_eq_self_of_isSimpleGroup_barSub h.hyp125 h.hL.1 hs
  have hL1 : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ := by
    have hne : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).1 hs.toNontrivial
    rw [hXL] at hne
    exact hne
  exact ⟨hXL, barSubBar2Equiv_of_isSimpleGroup h.hyp125 h.hL.1 hL1
    (isSimpleGroup_bar2_of_hyp18 h hXL)⟩

theorem isU4_barSub_cong {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) {f : ℕ}
    (hU : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) f) :
    conjClosure D.M L = L ∧ S17.nOf L = f ∧ 1 < f ∧
      (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] := by
  have hs : IsSimpleGroup
      ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hs
  have hU1 := hU
  rw [hXL] at hU1
  have hU' : IsU4 (Bar2 L) f := LieModel.of_mulEquiv e.symm hU1
  have hUX : IsU4 (Bar2 (conjClosure D.M L)) f := by
    rw [hXL]; exact hU'
  have hconcl : S17.Concl17_42 D L (conjClosure D.M L) p := h1742 L p h.hL.1 h.hp
  rcases hconcl with h1 | ⟨n, x, -, -, hXne, -, -⟩ | ⟨n, hU5, -, -, -, -⟩ |
    ⟨n, hshape4, hn1, hcong, -⟩ | ⟨n, hU4, hn1, hcong, -⟩
  · rcases h1 with hthin | ⟨n, hU3⟩ | hL3
    · exact absurd hthin (S17.not_thin8_of_isU4_bar2 hUX)
    · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hU3).2.1
        (by norm_num)
    · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hL3).1
        (by decide)
  · exact absurd hXL hXne
  · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hU5).2.1
      (by norm_num)
  · rcases hshape4 with hsp | hg2
    · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hsp).1
        (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hg2).1
        (by decide)
  · have hnf : n = f :=
      fieldExponent_eq_of_isChar2LieShape hUX S17.isChar2LieShape_PSU_four hU4
    exact ⟨hXL, S17.nOf_eq_of_isU4 hU', hnf ▸ hn1, hnf ▸ hcong⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
