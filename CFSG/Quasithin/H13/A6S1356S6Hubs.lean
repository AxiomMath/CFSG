module

public import CFSG.Quasithin.H13.A6S1356S6Q
public import CFSG.Quasithin.H13.A6S1356S6Fr
public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem input1356TwoS6_of_hubs
    (h1222 : Stmt12_2_2) (h13315 : Stmt13_3_15) : Input1356TwoS6 :=
  input1356TwoS6_of_sqtk (C124.c124StatementSQTK_of_e22 e22StatementNoN_proved) h1222
    (input1356TwoS6Block_of h13315)

theorem input1356Two_of_hubs
    (h1222 : Stmt12_2_2) (h13315 : Stmt13_3_15) : Input1356Two :=
  input1356Two_of h1222 (input1356TwoS6_of_hubs h1222 h13315)

end CFSG.Quasithin.H13.A6
