module

public import CFSG.Quasithin.Background.C124AsmZ3Final
public import CFSG.Quasithin.Background.C124YZAlt57
public import CFSG.Quasithin.Background.C124YZAlt6
public import CFSG.Quasithin.Background.C124BlkA7
public import CFSG.Quasithin.Background.C124BlkHat6
public import CFSG.Quasithin.Background.C124BlkL2
public import CFSG.Quasithin.Background.C124BlkAlt
public import CFSG.Quasithin.Background.C124YLA7Main
public import CFSG.Quasithin.Background.C124YLA6Main
public import CFSG.Quasithin.Background.C124YLL2Main
public import CFSG.Quasithin.Background.C124YLH6Main
public import CFSG.Quasithin.Background.FFCAssembly51
public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.Background.F918D9
public import CFSG.Quasithin.Background.SmithB51Sp4
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.SmithA36
public import CFSG.Quasithin.Background.C118NoOuter

public section

namespace CFSG.Quasithin.C124

theorem c124StatementSQTK_of_e23
    (hE23 : E2.E23Statement) (G : Type) [Group G] [Finite G] :
    C124StatementSQTK (G := G) :=
  c124StatementSQTK_of_spec_props theoremC118 hE23
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
    asA21SQTKSection asA36NoOddCover_holds spec4bL2_holds spec4bAlt5_holds
    spec4bAlt6b_holds spec4bAlt6c_holds spec4bAlt7_holds spec4bHat6_holds spec4bA7Four_holds
    spec4cL2_holds spec4cAlt5_holds spec4cAlt6_holds spec4cAlt7_holds spec4cHat6_holds
    spec4cA7Four_holds G

end CFSG.Quasithin.C124
