module

public import CFSG.Quasithin.Background.FFC11A
public import CFSG.Quasithin.Background.FFC11B

public section

namespace CFSG.Quasithin

namespace B69

theorem asB69NoOddCoverSL2 : AsB69NoOddCoverSL2 :=
  fun L H _ _ _ hL f hf hodd hH => noOddCoverSL2 L H hL f hf hodd hH

end B69

end CFSG.Quasithin
