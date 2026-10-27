module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cGraph
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Emb

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13

theorem l2Graph_of_reduced
    (hF : A312Facts) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (hG2 : FactG2Simple)
    (hiso : L2GraphIso) : L2Graph :=
  l2Graph_of hF CFSG.Quasithin.H13.VolI.a36ForSQTK_holds
    (a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
    (a39ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a39ForSQTKCat_proved)
    CFSG.Quasithin.H13.factMathieuOrders_holds
    CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2 h325 h328 hG2 hiso

end CFSG.Quasithin.Vol2.Ch11.SecB
