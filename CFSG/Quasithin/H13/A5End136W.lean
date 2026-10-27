module

public import CFSG.Quasithin.H13.A5Close1321c
public import CFSG.Quasithin.H13.U3L134W

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Quasithin

theorem end136_of_1332
    (h1323 : Input1323Two) (h1336 : Input1336) (h1332 : Stmt13_3_2) (hfin : Fin136) :
    End136 :=
  end136_of_fin h1323 h1336 (U3.stmt13_3_8_holds h1332) hfin

theorem input136_of_1332
    (h137 : Thm13_6_7) (h1326 : Input1326Two) (h1336 : Input1336) (h1323 : Input1323Two)
    (h1332 : Stmt13_3_2) (hfin : Fin136) : Input136 :=
  input136_of h137 h1326 h1336 (end136_of_1332 h1323 h1336 h1332 hfin)

end CFSG.Quasithin.H13.A5
