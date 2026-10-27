module

public import CFSG.Quasithin.H13.A6S1372L76N3c
public import CFSG.Quasithin.H13.A6S1372L76Oi2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

theorem lem1376NThree_of_c3 (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hC : Lem1376NThreeC3) : Lem1376NThree :=
  lem1376NThree_of h13315 h1356two hC
    (lem1376NThreeBlock_of h139 h37 h38 h13314 h13315 h1356two)

theorem lem1376Full_of_l32_c3
    (hL : Lem1376OddNCL32) (hC : Lem1376NThreeC3)
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h1337 : Stmt13_3_7) : Lem1376Full :=
  lem1376Full_of_l32_nThree hL (lem1376NThree_of_c3 h139 h37 h38 h13314 h13315 h1356two hC) hF h36
    h37 h38 h139 h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
