module

public import CFSG.RankThree.GF2n.Tim77.Cor2Alpha
public import CFSG.RankThree.GF2n.Tim77.Cor2AlphaInputs

public section

namespace CFSG.RankThree.GF2n.Tim77

theorem tim77AlphaBox_holds :
    Tim77AlphaBox :=
  fun _ _ _ _ hA hTI hroot hW hne =>
    cor2Alpha_of_rootType corBFine_holds corBListSimple_holds hA hTI hroot hW hne

end CFSG.RankThree.GF2n.Tim77
