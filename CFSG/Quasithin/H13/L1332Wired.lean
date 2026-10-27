module

public import CFSG.Quasithin.H13.L1332
public import CFSG.Quasithin.H13.FiveQuotientOddIndexProof

public section

namespace CFSG.Quasithin.H13

theorem stmt13_3_2_of_open
    (hD : LocalDoubleEmbeddingExclusion) (h137 : Stmt13_1_7)
    (h1312 : Stmt13_1_2_three) (h323 : Stmt3_2_3) (h1222 : Stmt12_2_2) (h1242 : Stmt12_4_2)
    (h1271 : Stmt12_7_1) (hL32 : L32NoIrrFour) : Stmt13_3_2 :=
  stmt13_3_2_of_inputs hD h137 h1312 h323 h1222 h1242 h1271 fiveQuotientOddIndexSolvable_holds
    hL32

end CFSG.Quasithin.H13
