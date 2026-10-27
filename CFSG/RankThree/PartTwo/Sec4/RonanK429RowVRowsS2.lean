module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVL44
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVSp64
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.Walter.J1Props

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSp)

theorem eight_SL4 : RowSOf429 (projSL 4 (GaloisField 2 2)) :=
  rowSOf429_of_noCfg fun _ _ _ hs hna ⟨φ⟩ => RowV.noCfgS429_projSL_four_four hs hna φ

theorem eight_Sp6_4 : RowSOf429 (projSp 3 (GaloisField 2 2)) :=
  rowSOf429_of_noCfg fun _ _ _ hs hna ⟨φ⟩ => RowV.noCfgS429_projSp_three_four hs hna φ

end CFSG.RankThree.PartTwo.Sec4.RonanK429V
