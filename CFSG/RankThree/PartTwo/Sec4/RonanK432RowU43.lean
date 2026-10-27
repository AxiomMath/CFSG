module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSU)

theorem outerRow_u43 [Finite (projSU 4 3 1)] : OuterRow (projSU 4 3 1) :=
  outerRow_of_not_three_dvd_outer CFSG.RankThree.PartTwo.Sec4.outU43_holds

theorem row_u43_of_listRow [Finite (projSU 4 3 1)] (hL : ListRow (projSU 4 3 1)) :
    RowOf (projSU 4 3 1) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm ⟨hL, outerRow_u43⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
