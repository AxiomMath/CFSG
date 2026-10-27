module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Br2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Br3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Finite W]

theorem conc4_135_bridge (h135 : W4Lem13_5) (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hf : FaithOn L (Wd L) (Cd L)) (hirr : IsIrrOn L (Wd L) (Cd L)) :
    Conc4_135 L (Wd L) (Cd L) (tcost t L (Wd L)) := by
  rcases bridge_ineq h135 hw2 c hf hirr with h | h
  · exact h
  · exact row1_exact hw2 c hf hirr h

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
