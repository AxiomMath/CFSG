module

public import CFSG.RankThree.PartOne.K133H.D4
public import CFSG.RankThree.PartOne.K133H.F4Ree
public import CFSG.RankThree.PartOne.K133H.G2Even
public import CFSG.RankThree.PartOne.K133H.G2Odd
public import CFSG.RankThree.PartOne.K133B.Heavy4

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG.RankThree.PartOne.K133B

theorem row8OddHeavy4_holds : Row8OddHeavy4 :=
  ⟨row8OddAt_leaf4_zero, row8OddAt_leaf7_five, row8OddAt_leaf7_eight, row8OddAt_leaf7_nine⟩

end CFSG.RankThree.PartOne.K133H
