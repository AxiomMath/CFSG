module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsRest
import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamD4
import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamOmegaList
import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamOmegaOuter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

theorem k332RowsRest_holds :
    K332RowsRest where
  list_trialityD4 := listRow_trialityD4
  outer_trialityD4 := outerRow_trialityD4
  list_pomegaMinus8 := listRow_pomegaMinus8
  outer_pomegaMinus8 := outerRow_pomegaMinus8
  list_pomegaOdd7 := listRow_pomegaOdd7
  outer_pomegaOdd7 := outerRow_pomegaOdd7

theorem k332Rows_holds :
    K332Rows :=
  k332Rows_of_rest k332RowsRest_holds

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
