module

public import CFSG.Quasithin.H13.L32AKG1468b
public import CFSG.Quasithin.H13.L32AKG1468h

public section

namespace CFSG.Quasithin.H13.KGRu

open CFSG.Open CFSG.QuasithinUnique

theorem kg1468TwoRu_holds :
    KG1468TwoRu := by
  intro G _ _ Y hq hRu z hzY _ hzC _ E hEO hEe hE8 hzE hEZ hcomm hy hS
  obtain ⟨y, hyK, hy3, hyN, hyf⟩ := hy
  obtain ⟨S, hS, hSN, hSz⟩ := hS
  exact normalizer_quot_sl32 hq hRu hzY hzC hEO hEe hE8 hzE hEZ hcomm hyK hy3 hyN hyf hS hSN hSz

end CFSG.Quasithin.H13.KGRu
