module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {K : Type*} [Field K]

theorem exists_toPGL_eq_of_pow_three {g : PGL2 K} (hg : g ^ 3 = 1) :
    ∃ x : PSL2 K, Matrix.ProjectiveSpecialLinearGroup.toPGL x = g :=
  CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_pow_odd (by decide) hg

variable [Finite K]

theorem pglAction_injective : Function.Injective (pglAction K) :=
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K

theorem isInnerAut_of_mem_inndiag_of_pow_three {α : MulAut (PSL2 K)}
    (hα : α ∈ (stdPinnedPSL2 K).inndiag) (hα3 : α ^ 3 = 1) : IsInnerAut α := by
  obtain ⟨g, rfl⟩ := hα
  have hg3 : g ^ 3 = 1 := pglAction_injective (by rw [map_pow, hα3, map_one])
  obtain ⟨x, rfl⟩ := exists_toPGL_eq_of_pow_three hg3
  exact ⟨x, (pglAction_toPGL K x).symm⟩

theorem isField_of_pow_three_of_not_inner {α : MulAut (PSL2 K)} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) : (stdPinnedPSL2 K).IsField α := by
  rcases hasKind_psl2_diagonal_or_field_of_pow_three_eq_one hα3 hout with h | h
  · obtain ⟨hD, hn⟩ := h
    exact absurd (isInnerAut_of_mem_inndiag_of_pow_three hD hα3) hn
  · exact h

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

theorem inducesKind_field_of_pow_three {x : G} (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L) (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K) :
    InducesKind L (stdPinnedPSL2 K) e x .field := by
  obtain ⟨hx, -⟩ := id hout
  exact ⟨hx, isField_of_pow_three_of_not_inner (inducedAutHom_pow_eq_one L e hx hx3)
    ((not_isInnerAut_inducedAutHom_iff L e hx).mpr hout)⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
