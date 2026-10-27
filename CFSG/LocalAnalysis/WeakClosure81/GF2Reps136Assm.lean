module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136S

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem conc_alt3 (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) (hT : Tcl Y L)
    (hs : SumOfAtMostThreeNat L (Wd L) (Cd L))
    (htr : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L, ∃ g ∈ Y ⊓ Subgroup.normalizer (L : Set (MulAut W)),
      I₂ = I₁.map g.toMonoidHom) :
    Conc4_136W Y t L := by
  refine ⟨lemmaS c.comp.1 (comm_top_of_component c.std hw2 c.comp), ?_,
    Or.inr (Or.inr (Or.inl ⟨c.comp, hs, htr⟩))⟩
  intro g hg hgN
  have hne : L.map (MulAut.conj g).toMonoidHom ≠ L := fun h =>
    hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hcomp := CFSG.LargeExtraspecial.S5.isComponentOf_map_conj c.comp hg
  refine ⟨?_, hT g hg hgN⟩
  rw [Subgroup.commutator_comm]
  exact CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hcomp c.comp hne

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
