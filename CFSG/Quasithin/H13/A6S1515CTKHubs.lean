module

public import CFSG.Quasithin.H13.GoldschmidtCTKWire
public import CFSG.Quasithin.H13.A6S1356S6Q
public import CFSG.Quasithin.H13.A6S1356S6Fr
public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem input13515CTK_of_hubs
    (h1222 : Stmt12_2_2) (h13315 : Stmt13_3_15) : Input13515CTK :=
  input13515CTK_of_lemmas h13315 <| input1356Two_of h1222 <|
    input1356TwoS6_of_sqtk (C124.c124StatementSQTK_of_e22 e22StatementNoN_proved) h1222
      (input1356TwoS6Block_of h13315)

end CFSG.Quasithin.H13.A6
