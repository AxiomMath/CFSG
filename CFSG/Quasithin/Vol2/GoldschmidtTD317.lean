module

public import CFSG.Quasithin.EmptyFaithful.LRed10KerN
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved

public section

namespace CFSG.Quasithin

theorem e23Nonsolvable_proved
    : E2.E23Nonsolvable :=
  GE23.e23Nonsolvable_of_inputs B15P4.asB15Part4
    (B69.asB69Component_of_deep_inputs_fourNoN asB42_holds asA21SQTKSection e22StatementNoN_proved
      (B69.asB69DeepInputsFour_holds e22StatementNoN_proved))
    (B69.b69One_of_Sp4NoN asB42_holds B15P4.asB15Part4 asA21SQTKSection e22StatementNoN_proved
      B69.noStrongSp4)
    e22StatementNoN_proved

theorem as317SylowNonsolvable_proved
    : AS317SylowNonsolvable :=
  LRed10.as317SylowNonsolvable_of_e23_noN e23Nonsolvable_proved e22StatementNoN_proved

theorem as317Sylow_proved
    : AS317Sylow :=
  as317Sylow_of_nonsolvable as317SylowNonsolvable_proved

end CFSG.Quasithin
