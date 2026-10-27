module

public import CFSG.Quasithin.H13.A6S1372L76Of4
public import CFSG.Quasithin.H13.A6S1372L76V
public import CFSG.Quasithin.H13.A6S1372L76X

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

theorem lem1376L1KSmallOdd_of_L32 (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hL : Lem1376OddNCL32) : Lem1376L1KSmallOdd :=
  lem1376L1KSmallOdd_of (lem1376L1KSmallOddComm_of h139 h37 h38 h13315)
    (lem1376L1KSmallOddNC_of (lem1376OddNCA5_of h139 h37 h38 h13315)
      (lem1376OddNCBig_of h139 h37 h38 h13315 h1356two) hL)

theorem lem1376L1KSmall_of_L32 (hF : A318Facts)
    (h36 : A36ForSQTK) (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hL : Lem1376OddNCL32) :
    Lem1376L1KSmall :=
  lem1376L1KSmall_of (lem1376L1KSmallEven_of hF h36 h38 h13315 h1356two)
    (lem1376L1KSmallOdd_of_L32 h139 h37 h38 h13315 h1356two hL)

theorem lem1376Full_of_atoms
    (hL : Lem1376OddNCL32) (h3 : Lem1376NThree) (h5 : Lem1376Five) (hF : A318Facts)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h139 : Stmt13_3_9)
    (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1337 : Stmt13_3_7) : Lem1376Full :=
  lem1376Full_of (lem1376L1K_of (lem1376L1KSmall_of_L32 hF h36 h139 h37 h38 h13315 h1356two hL)
    hF h36 h38 h13315 h1356two) h3 h5 h37 h38 h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
