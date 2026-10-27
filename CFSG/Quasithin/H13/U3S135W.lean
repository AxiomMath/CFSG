module

public import CFSG.Quasithin.H13.U3S135
public import CFSG.Quasithin.H13.A5RawNat

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem stmt13_3_5_of_1332
    (h1332 : Stmt13_3_2) (h12213 : Stmt12_2_13) (h331 : Stmt3_3_1)
    (h1327 : A5.Stmt13_2_7) : A6.Stmt13_3_5 :=
  stmt13_3_5_of h1332 h12213 h331 h1327 (A5.stmt13_3_2_three_A5_of h1332)

theorem stmt13_3_6_of_1332
    (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h331 : Stmt3_3_1)
    (h1327 : A5.Stmt13_2_7) : A6.Stmt13_3_6 :=
  stmt13_3_6_of h1332 h1222 h12213 h331 h1327 (A5.stmt13_3_2_three_A5_of h1332)

end CFSG.Quasithin.H13.U3
