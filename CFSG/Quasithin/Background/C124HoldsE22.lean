module

public import CFSG.Quasithin.Background.C124Holds
public import CFSG.Quasithin.Background.GoldschmidtE23Final
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.EmptyFaithful.A38c13FFC
public import CFSG.Quasithin.Background.GoldschmidtB69DeepFour

public section

namespace CFSG.Quasithin.C124

theorem e23Statement_of_e22
    (h22 : E2.E22StatementNoN) : E2.E23Statement :=
  E2.e23Statement_of_nonsolvable <| GE23.e23Nonsolvable_of_inputs B15P4.asB15Part4
    (B69.asB69Component_of_deep_inputs_fourNoN asB42_holds asA21SQTKSection h22
      (B69.asB69DeepInputsFour_holds h22))
    (B69.b69One_of_Sp4NoN asB42_holds B15P4.asB15Part4 asA21SQTKSection h22 B69.noStrongSp4) h22

theorem c124StatementSQTK_of_e22
    (h22 : E2.E22StatementNoN) (G : Type) [Group G] [Finite G] : C124StatementSQTK (G := G) :=
  c124StatementSQTK_of_e23 (e23Statement_of_e22 h22) G

end CFSG.Quasithin.C124
