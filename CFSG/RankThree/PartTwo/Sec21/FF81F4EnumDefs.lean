module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Check

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Simplicity.TitsBits
open CFSG.RankThree.PartTwo.Sec4.Item434F42
open CFSG.RankThree.PartOne.SEITZX (letterOfCode)

@[expose] def letterGB : Array ℕ := ((List.range 8).map fun l => (letterOfCode l).bits).toArray

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
