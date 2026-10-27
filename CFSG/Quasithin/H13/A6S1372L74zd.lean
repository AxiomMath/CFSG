module

public import CFSG.Quasithin.H13.A6S1372L74j
public import CFSG.Quasithin.H13.A6S1372L74q
public import CFSG.Quasithin.H13.A6S1372L74zc
public import CFSG.Quasithin.H13.A6S1372L74h

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem lem1374One_holds
    (h1227 : U3.Stmt13_2_2_7) (h1337 : Stmt13_3_7) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) (h139 : Stmt13_3_9) (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h1352 : Stmt13_5_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hF : A318Facts) (h36 : A36ForSQTK) (h51 : AsB51) : Lem1374One :=
  lem1374One_of (lem1374OneDiag_of h1227 h1337) (lem1374OneOdd_of h1227 h13315 h1356two)
    (lem1374OneFinal_of (lem1374OneFinalZ3_of h1227 h13315 h1356two)
      (lem1374OneFinalSimple_of (lem1374OneSimpleMod_of h51) h1227 h1337 h13315 h1356two))
    h13315 h1356two h13314 h139 h1222 h323 h1352 h37 h38 hF h36

end CFSG.Quasithin.H13.A6
