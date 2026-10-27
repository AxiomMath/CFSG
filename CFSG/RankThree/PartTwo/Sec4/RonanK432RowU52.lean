module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU52Wreath
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSU)

theorem outerRow_u52 : OuterRow (projSU 5 2 1) :=
  outerRow_of_not_three_dvd_outer
    (by rw [Item434SmallTwoIV.card_outer_projSU_five_two]; norm_num)

theorem row_u52 : RowOf (projSU 5 2 1) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm ⟨listRow_u52, outerRow_u52⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
