module

public import CFSG.RankThree.PartOne.F106.NoQD32L3U3At
public import CFSG.RankThree.PartOne.F106.NoQD32NAU6

public section

namespace CFSG.RankThree.PartOne.F106

theorem noQD32AtThree_holds :
    NoQD32AtThree :=
  noQD32AtThree_of_psu6 fun _ _ hT _ _ hE h => u6_abelian_false hT hE h

end CFSG.RankThree.PartOne.F106
