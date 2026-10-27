module

public import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdHJMain
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155UpPi
import CFSG.RankThree.PartTwo.Sec15.Liebeck155Sections
public import CFSG.RankThree.PartTwo.Sec15.Liebeck159Five
public import CFSG.RankThree.PartTwo.Sec14.Ronan149Holds
public import CFSG.RankThree.PartTwo.Sec15.Ronan155YFieldW
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenHolds
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SFrontier

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckClosed

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

theorem y4CoreMemSolvR_of_134
    (h134 : Item134) : Y4CoreMemSolvR :=
  LiebeckY4.y4CoreMemSolvR_of_route Ronan148M.item148R_holds Ronan149.item149S14_holds
    Ronan149.item145BotS14_holds h134 Sec11.Close.closed_sec4Item4_5
    Sec11.Close.closed_sec4Item4_8 Ronan148C.step148Core_holds Ronan148M.step148Point_holds
    Ronan148M.step148KType_holds Ronan148M.step148Lift_holds

theorem step155UpPiNHJR_of_134
    (h134 : Item134) : Step155UpPiNHJR :=
  Liebeck155.step155UpPiNHJR_of_sections Ronan155Y.y4LThreePiNHJR_holds Ronan148M.item148R_holds
      h134 Sec11.Close.closed_sec4Item4_8 Ronan149.item145BotS14_holds
      (Liebeck155.evenPerfectSection_of Ronan148T.evenSimpleList_holds)

theorem item158Y0R_of_131_134
    (h131 : Item131) (h134 : Item134) : Item158Y0R :=
  Liebeck158.item158Y0R_of_items Ronan138S.item138N_holds h131 h134
    Sec11.Close.closed_sec4Item4_8 Ronan148M.item148R_holds
    Sec11.Close.closed_sec4Item4_1LargePrime

theorem step159FiveR_of_134
    (h134 : Item134) : Step159FiveR :=
  Liebeck159.step159FiveR_of h134 Sec11.Close.closed_sec4Item4_8 Ronan138S.item138N_holds
    Sec11.Close.closed_sec4Item4_1LargePrime

theorem y4CoreMemSolvR_holds
    : Y4CoreMemSolvR := by
  obtain ⟨-, -, -, -, -, -, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact y4CoreMemSolvR_of_134 h134

theorem step155UpPiNHJR_holds
    : Step155UpPiNHJR := by
  obtain ⟨-, -, -, -, -, -, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact step155UpPiNHJR_of_134 h134

theorem item158Y0R_holds
    : Item158Y0R := by
  obtain ⟨-, -, -, -, -, -, -, h131, h134, -, -⟩ := Ronan148M.closedInputs
  exact item158Y0R_of_131_134 h131 h134

theorem step159FiveR_holds
    : Step159FiveR := by
  obtain ⟨-, -, -, -, -, -, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact step159FiveR_of_134 h134

end CFSG.RankThree.PartTwo.Sec15.LiebeckClosed
