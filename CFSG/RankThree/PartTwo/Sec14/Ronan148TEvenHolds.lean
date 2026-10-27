module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenFinalAll

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T


theorem evenSimpleListL3_holds : EvenSimpleListL3 :=
  evenSimpleListL3_of_irred evenSL3Irred

theorem evenSimpleList_holds : EvenSimpleList :=
  evenSimpleList_of_L3 evenSimpleListL3_holds

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
