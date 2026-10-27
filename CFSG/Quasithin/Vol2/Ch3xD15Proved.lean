module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved

public section

namespace CFSG.Quasithin

theorem b69One_proved
    : B69One :=
  B69.b69One_of_Sp4NoN asB42_holds B15P4.asB15Part4 asA21SQTKSection e22StatementNoN_proved
    B69.noStrongSp4

theorem d125NonsolvableSQTK_proved
    : D125NonsolvableSQTK :=
  d125NonsolvableSQTK_of_b69One b69One_proved

theorem d15AsPrintedSQTK_proved
    : D15AsPrintedSQTK :=
  d15AsPrintedSQTK_of_nonsolvable d125NonsolvableSQTK_proved

end CFSG.Quasithin

end
