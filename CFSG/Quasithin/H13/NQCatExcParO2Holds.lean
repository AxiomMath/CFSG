module

public import CFSG.Quasithin.H13.NQCatExcParO2
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BKG

public section

namespace CFSG.Quasithin.H13.NQCat

theorem factExcParabolicO2Ne_holds :
    FactExcParabolicO2Ne :=
  fun _ _ _ L P m hm hL hP hPSL => ExcPar.pCore_perfectCore_ne_bot L P m hm hL hP hPSL

end CFSG.Quasithin.H13.NQCat
