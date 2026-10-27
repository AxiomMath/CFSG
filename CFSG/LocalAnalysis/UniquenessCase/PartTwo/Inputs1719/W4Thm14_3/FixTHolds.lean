module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTSkeleton
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTSz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExtHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem k14_3FixT_of_ext (hExt : K14_3Ext) : K14_3FixT := by
  intro W _ _ hW Y L T n hO hB hLY hLn hshape hn hT
  refine fixV_ne_fixV_sup_of_irrSet hW hO hB hLY hLn
    (isComponentOf_of_isL2_or_isSz hLY hLn hshape) hT fun J hJ hJC => ?_
  rcases hshape with h2 | hsz
  · exact exists_borelMoves_of_isL2 hExt hW h2 hn hJ hJC
  · exact exists_borelMoves_of_isSz hW hsz hJ hJC

theorem k14_3FixT_holds : K14_3FixT :=
  k14_3FixT_of_ext k14_3Ext_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
