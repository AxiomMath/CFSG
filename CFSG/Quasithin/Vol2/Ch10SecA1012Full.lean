module

public import CFSG.Quasithin.Vol2.Ch10SecA1012
public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrth
public import CFSG.Quasithin.Vol2.Ch10SecAFactsSz

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem factsTorus_holds : FactsTorus :=
  ⟨factSzTorus_holds, factOrthTorus_holds⟩

theorem stmt10_1_2_of_facts10_1
    (hF : Facts10_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h3228 : TmpL6_3_2_2_eight)
    (hshape : Stmt7_0_1_shape) (h42 : AsB42) (h51 : AsB51) (h154 : AsB15Part4)
    (h116 : ASInputs.AS_I_1_6_one) (h3210 : TmpL6_3_2_10_nine) (h331 : Stmt3_3_1)
    (he23 : E2.E23Statement) : Stmt10_1_2 :=
  stmt10_1_2_of hF factsTorus_holds h37 h38 h322 h3228 hshape h42 h51 h154 h116 h3210 h331 he23

end CFSG.Quasithin.Vol2.Ch10.SecA
