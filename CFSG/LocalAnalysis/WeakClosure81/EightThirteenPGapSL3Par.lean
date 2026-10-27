module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSL3ParAux2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem rankTwoParabData_slThree_unitriangular {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 4) :
    RankTwoParabData (unitriangular 3 F : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :=
  wcgapsp_rankTwoParabData_slThree_unitriangular hF

end CFSG.LocalAnalysis.WeakClosure81

end
