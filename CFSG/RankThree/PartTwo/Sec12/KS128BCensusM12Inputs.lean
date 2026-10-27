module

public import CFSG.RankThree.PartTwo.Toolkit.M12LocalInputs
public meta import CFSG.RankThree.PartTwo.Toolkit.M12LocalInputs

public section

namespace CFSG.RankThree.PartTwo.Sec12.BCensus

open CFSG.RankThree.PartTwo.Toolkit.M12

@[expose] def czCheck : Bool :=
  allIdx.all fun k => !predC [zT] (prodT k) || predN [xT, yT] P0T (prodT k)

end CFSG.RankThree.PartTwo.Sec12.BCensus
