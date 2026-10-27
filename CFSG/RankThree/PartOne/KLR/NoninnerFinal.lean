module

public import CFSG.RankThree.PartOne.KLR.Native
public import CFSG.RankThree.PartOne.KLR.NoninnerCore
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.RankThree.PartOne.KLR


theorem largeReeNoninnerCore : LargeReeNoninnerCore := fun _ ha _ _ _ _ hK _ hp hp3 =>
  localCoreTrivialOn_noninner ha hK hp hp3

end CFSG.RankThree.PartOne.KLR
