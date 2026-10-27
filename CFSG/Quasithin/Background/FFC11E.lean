module

public import CFSG.Quasithin.Background.FFC11D
public import CFSG.Quasithin.Background.FFC11F

public section

namespace CFSG.Quasithin

namespace B69

theorem asB69SectionB42_of (hB42 : AsB42) (hA21 : AsA21SQTKSection) : AsB69SectionB42 :=
  fun _ _ _ hV _ _ _ _ _ hH _ hW => sectionB42_of hB42 hA21 hV hH hW

theorem asB69NoRankTwoSL3_proved : AsB69NoRankTwoSL3 :=
  fun _ _ _ hV _ _ _ _ _ hH _ hW hc => noRankTwoSL3_of hV hH hW hc

end B69

end CFSG.Quasithin
