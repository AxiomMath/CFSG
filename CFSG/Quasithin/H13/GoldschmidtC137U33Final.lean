module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Case
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Fin
public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.Background.F918D9
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.SmithB51Sp4
public import CFSG.Quasithin.Background.SmithA36
public import CFSG.Quasithin.Background.FFCAssembly51

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin


theorem c137CaseU33_final
    (hC132 : ASInputs.AS_C_1_32) : C137CaseU33 :=
  c137CaseU33_of
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
    asA21SQTKSection asA36NoOddCover_holds H13.VolI.g2NaturalCover_holds
    H13.g2DerivedNormalizerZorn hC132 u33G2Facts_holds

end CFSG.Quasithin.H13.U3.GC137
