module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4EnumDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.RankThree.PartTwo.Sec4.Item434F42
open CFSG.RankThree.PartOne.SEITZX (codeBits wordOfCodes letterOfCode)

@[expose] def flipCode (c : ℕ) : ℕ := if c < 4 then 3 - c else 11 - c

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
