module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapesSzSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


open CFSG.ComponentClassification.CatLeafProof
  (lieModel_eq_of_isChar2LieShape fieldExponent_eq_of_isChar2LieShape)

theorem isSp4_or_isG2_bar2_cong_more {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) {f : ℕ}
    (hS : IsSp4 (Bar2 (conjClosure D.M L)) f ∨ IsG2 (Bar2 (conjClosure D.M L)) f) :
    conjClosure D.M L = L ∧ S17.nOf L = f ∧ 1 < f ∧ Odd f ∧
      (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] ∧ D.k = 1 ∧
      S17.P17_42_more D (conjClosure D.M L) f := by
  set X : Subgroup G := conjClosure D.M L with hXdef
  have hsimple : IsSimpleGroup (Bar2 X) := by
    rcases hS with hsp | hg2
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp
    · exact (CFSG.LieType.Simplicity.fam_g2_simplicity (Bar2 X) 2 f
        (LieModel.chevalleyExceptionalModel hg2 (by decide))).2
  have hXL : X = L := conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsimple
  have hconcl : S17.Concl17_42 D L X p := h1742 L p h.hL.1 h.hp
  rcases hconcl with h1 | ⟨n, x, -, -, hXne, -, -⟩ | ⟨n, hU5, -, -, -, -⟩ |
    ⟨n, hshape4, hn1, hodd, hcong, hk1, hmore⟩ | ⟨n, hU4, -, -, -⟩
  · rcases h1 with hthin | ⟨n, hU3⟩ | hL3
    · rcases hS with hsp | hg2
      · exact absurd hthin (S17.not_thin8_of_isSp4_bar2 hsp)
      · exact absurd hthin (S17.not_thin8_of_isG2_bar2 hg2)
    · rcases hS with hsp | hg2
      · exact absurd (lieModel_eq_of_isChar2LieShape hsp S17.isChar2LieShape_PSp hU3).1
          (by decide)
      · exact absurd (lieModel_eq_of_isChar2LieShape hg2 S17.isChar2LieShape_G2 hU3).1
          (by decide)
    · rcases hS with hsp | hg2
      · exact absurd (lieModel_eq_of_isChar2LieShape hsp S17.isChar2LieShape_PSp hL3).1
          (by decide)
      · exact absurd (lieModel_eq_of_isChar2LieShape hg2 S17.isChar2LieShape_G2 hL3).1
          (by decide)
  · exact absurd hXL hXne
  · rcases hS with hsp | hg2
    · exact absurd (lieModel_eq_of_isChar2LieShape hsp S17.isChar2LieShape_PSp hU5).1 (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hg2 S17.isChar2LieShape_G2 hU5).1 (by decide)
  · have hnf : n = f := by
      rcases hS with hsp | hg2
      · rcases hshape4 with hspn | hg2n
        · exact fieldExponent_eq_of_isChar2LieShape hsp S17.isChar2LieShape_PSp hspn
        · exact absurd (lieModel_eq_of_isChar2LieShape hsp S17.isChar2LieShape_PSp hg2n).1
            (by decide)
      · rcases hshape4 with hspn | hg2n
        · exact absurd (lieModel_eq_of_isChar2LieShape hg2 S17.isChar2LieShape_G2 hspn).1
            (by decide)
        · exact fieldExponent_eq_of_isChar2LieShape hg2 S17.isChar2LieShape_G2 hg2n
    obtain rfl := hnf
    have hnof : S17.nOf L = n := by
      rw [← hXL]
      rcases hS with hsp | hg2
      · exact S17.nOf_eq_of_isSp4 hsp
      · exact S17.nOf_eq_of_isChar2LieShape hg2 S17.isChar2LieShape_G2
    exact ⟨hXL, hnof, hn1, hodd, hcong, hk1, hmore⟩
  · rcases hS with hsp | hg2
    · exact absurd (lieModel_eq_of_isChar2LieShape hsp S17.isChar2LieShape_PSp hU4).1 (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hg2 S17.isChar2LieShape_G2 hU4).1 (by decide)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
