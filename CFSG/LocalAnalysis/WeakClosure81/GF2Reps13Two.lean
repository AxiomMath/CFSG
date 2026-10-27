module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoI
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

theorem w4Lem13_2Min_holds : W4Lem13_2Min := by
  intro W _ _ hW t ht hrk p P hp hP hne hn hc hmin
  exact w16h_minLe w4Lem13_1_holds (Nat.card P) W hW t ht hrk p P hp hP hne hn hc le_rfl hmin

end CFSG.LocalAnalysis.WeakClosure81
