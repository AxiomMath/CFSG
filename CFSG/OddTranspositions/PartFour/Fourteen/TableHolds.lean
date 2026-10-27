module

public import CFSG.OddTranspositions.PartFour.Fourteen.Statements
import CFSG.OddTranspositions.PartFour.Fourteen.Table
import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Pair
import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five

public section

namespace CFSG.OddTranspositions.PartFour

theorem ascListTable_holds : AscListTable :=
  ascListTable_of_rows (fun _ _ _ hP => noSqE1_of_isO4Minus5Pair hP)
    fun _ _ _ _ _ hn _ hsym hnd hM => noSqE1_of_fischerCentralQuotientModel_five hn hsym hnd hM

end CFSG.OddTranspositions.PartFour
