module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148CFinal
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowCharThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

section Certs

theorem k148OpenRows_holds : K148OpenRows :=
  K148OpenRows.ofLie k148OpenRowsLie_holds

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan148C

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open CFSG.RankThree.PartTwo.Sec4.Ronan148C

section Certs

theorem step148Core_of_seitz
    (hS : Seitz82Rest) : Step148Core :=
  step148Core_of_open hS k148OpenRows_holds

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148C
