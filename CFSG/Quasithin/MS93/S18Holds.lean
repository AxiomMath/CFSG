module

public import CFSG.Quasithin.MS93.S36S18
public import CFSG.Quasithin.MS93.FFMain

public section

namespace CFSG.Quasithin.MS93

theorem ms18Int_holds :
    MS18Int :=
  fun hF _ hα hVc hV2 hker hsq hU hVU =>
    isSumOfNaturalModulesVia_two_of_ext ms14AS_holds hF hα hVc hV2 hker hsq hU hVU

theorem s18_holds :
    S18 :=
  s18_of ms18Int_holds

end CFSG.Quasithin.MS93
