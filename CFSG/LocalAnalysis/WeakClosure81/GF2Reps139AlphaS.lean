module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaSCnt
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaSThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.alpha_not_symplectic (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥)
    (hB : HasSympForm K) : False := by
  by_cases h4 : 4 ≤ n
  · exact Std139.alpha_not_symplectic_ge4 hw2 S h4 hK hirr hB
  · exact Std139.alpha_not_symplectic_three hw2 S (by omega) hK hirr hB

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
