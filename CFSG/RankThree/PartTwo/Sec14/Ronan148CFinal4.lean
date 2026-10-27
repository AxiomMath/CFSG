module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148CFinal3
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CSeitzHolds

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open CFSG.RankThree.PartTwo.Sec4.Ronan148C

section Certs

theorem step148Core_holds
    : Step148Core :=
  step148Core_of_seitz seitz82Rest_holds

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148C
