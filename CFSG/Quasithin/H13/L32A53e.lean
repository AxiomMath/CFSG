module

public import CFSG.Quasithin.H13.L32A53d
public import CFSG.Quasithin.H13.L32A74b
public import CFSG.Quasithin.H13.VolIA36

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem T53.thm14_5_3_reduced
    (h13314 : A6.Stmt13_3_14) (h55 : Lemma14_5_5Q)
    (h1434 : Lemma1434One) (hSym : Lemma14_5_8Sym) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) :
    Thm14_5_3 :=
  T53.thm14_5_3_of_inputs (lemma14_7_4_two_three_of h1222 h1332 h13314) h55
    VolI.a36ForSQTK_holds h1434 hSym h1222 h1332 (U3.stmt13_3_4_of h1332)

end CFSG.Quasithin.H13.L32A

end
