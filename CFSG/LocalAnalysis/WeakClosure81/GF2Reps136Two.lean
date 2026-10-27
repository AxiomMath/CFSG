module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoB5

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem case_T_or_two (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) :
    Tcl Y L ∨ ∃ L' : Subgroup (MulAut W), Conc4_136W Y t L' := by
  by_cases hT : Tcl Y L
  · exact Or.inl hT
  · right
    have h : ∃ g ∈ Y, g ∉ Subgroup.normalizer (L : Set (MulAut W)) ∧
        commSub (Wd L) (Lc L g) ≠ ⊥ := by
      by_contra hcon
      exact hT fun g hg hgN => by_contra fun hne => hcon ⟨g, hg, hgN, hne⟩
    obtain ⟨g, hgY, hgN, hne⟩ := h
    exact case_two_of_swap hw2 (S := ⟨c, hfix, hgY, hgN, hne⟩)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
