module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Master1
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Master2
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Cover
public import CFSG.LocalAnalysis.WeakClosure81.W183K3CoverTwo
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Disp
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Big
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Rows
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Odd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (ListBNonabelian)
open W183K3

variable {G : Type} [Group G] [Finite G]

theorem Br3Rows.of_br1Rows (rows : Br1Rows) (h210 : Asch2_10) (g1syl : FinG1Syl)
    (g11cov : FinG11Cov) : Br3Rows :=
  ⟨rows.a6, rows.g1, g1syl, rows.g3, rows.g4l34, rows.g4a6, asch6_5Odd_holds, rows.h65f, h210,
    g11cov⟩

theorem br3Leaves_holds : Br3Leaves :=
  ⟨br3MasterOne_holds, br3MasterTwo_holds, br3CoverOne_holds, br3CoverTwo_holds⟩

theorem tail1812FourFreeKStar_holds
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hO : LieOrderFormulasInput) (hB : ListBNonabelian) (h3 : Tail1812Two_AS G)
    (rows : Br3Rows) : Tail1812FourFreeKStar G :=
  tail1812FourFreeKStar_of_big hB h3
    (tail1812FourFreeKStarBig_of_leaves hGA hO hB rows br3Leaves_holds)

end CFSG.LocalAnalysis.WeakClosure81

end
