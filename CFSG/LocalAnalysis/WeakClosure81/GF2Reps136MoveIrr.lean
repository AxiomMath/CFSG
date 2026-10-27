module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveB2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveB3
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Assm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem case_move_irr (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hmove : ∃ I ∈ irrSet L, I.map t.toMonoidHom ≠ I) : Conc4_136W Y t L := by
  obtain ⟨I, hI, hne⟩ := hmove
  have S : Move136 Y t L I := ⟨c, hI, hne⟩
  have hT := move_Tcl hw2 S
  exact conc_alt3 hw2 c hT (move_sum_of_nat hw2 S hT) (move_trans hw2 S hT)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
