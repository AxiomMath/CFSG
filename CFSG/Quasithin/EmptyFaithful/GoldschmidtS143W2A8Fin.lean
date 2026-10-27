module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2A8Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Fin

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace S143

namespace InspW2

theorem inspW_cards_a8
    (hL34 : ResW fun L _ => StatedClassicalModel L .PSL 3 2 2)
    (hU34 : ResW fun L _ => StatedClassicalModel L .PSU 3 2 2)
    (hSz8 : ResW fun L _ => SuzukiModel L 2 3) (hL33 : ResW Insp7.L33Fam)
    (hM12 : ResW Insp7.M12Fam) : InspW :=
  inspW_cards hL34 hU34 resW_a8 hSz8 hL33 hM12

end InspW2

end S143

end CFSG.Quasithin
