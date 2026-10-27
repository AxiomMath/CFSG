module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SumNat
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Bridge135

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Finite W]

theorem case_T_conc (h135 : W4Lem13_5) (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) (hT : Tcl Y L) : Conc4_136W Y t L := by
  have hLp : ⁅L, L⁆ = L :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr c.comp.2.2.1)
  have hWds : commSub (Wd L) L = Wd L := by
    refine le_antisymm (commSub_mono le_top le_rfl) ?_
    exact s13_perfect_chain L hLp (commSub (Wd L) L) (Wd L) ⊤ le_rfl le_rfl
  refine ⟨lemmaS c.comp.1 (comm_top_of_component c.std hw2 c.comp), ?_, ?_⟩
  · intro g hg hgn
    have hcomp : IsComponentOf (L.map (MulAut.conj g).toMonoidHom) Y :=
      CFSG.LargeExtraspecial.S5.isComponentOf_map_conj c.comp hg
    have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := by
      intro heq
      exact hgn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm)
    exact ⟨CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne c.comp hcomp hne,
      hT g hg hgn⟩
  · by_cases hirr : IsIrrOn L (Wd L) (Cd L)
    · exact Or.inr (Or.inr (Or.inr
        ⟨⟨hWds, hirr⟩, c.Lt, c.comp,
          conc4_135_bridge h135 hw2 c (faithful_on_wstar hw2 c hT) hirr⟩))
    · exact Or.inr (Or.inr (Or.inl
        ⟨c.comp, sum_of_nat hw2 c hfix hT hirr,
          transitive_on_irr hw2 c hfix hT⟩))

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
