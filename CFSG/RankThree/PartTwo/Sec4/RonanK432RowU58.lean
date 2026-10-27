module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU58List
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU58Outer
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSU)

theorem row_u58 : RowOf (projSU 5 2 3) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm ⟨listRow_u58, outerRow_u58⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
