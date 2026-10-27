module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148CCore
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowsAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open CFSG.RankThree.PartTwo.Sec4.Ronan148C

section Certs

theorem step148Core_of_open
    (hS : Seitz82Rest) (O : K148OpenRows) : Step148Core :=
  step148Core_of_rowsS (k148RowsS_of_open hS O)

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148C
