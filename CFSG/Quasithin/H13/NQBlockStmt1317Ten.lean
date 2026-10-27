module

public import CFSG.Quasithin.H13.NQBlockStmt1317Open
public import CFSG.Quasithin.H13.NQBlockEscapingPair
public import CFSG.Quasithin.H13.GoldschmidtU3ThreeCase
public import CFSG.Quasithin.Vol2.GoldschmidtC58Proved
public import CFSG.Quasithin.EmptyFaithful.S151Ch3Bridge

public section

namespace CFSG.Quasithin.H13.NQBlock

open CFSG.Open CFSG.QuasithinUnique

theorem stmt13_1_7_of_ten
    (h1323 : Stmt13_1_2_three) (h1001 : Stmt10_0_1) (h3214 : Stmt3_2_14)
    (h56 : AsB56) (h317 : Theorem317Statement)
    (h3 : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G)
    : Stmt13_1_7 :=
  stmt13_1_7_of_open h1323 h3214 h56 h317 h3 (stmtEscapingPairExcluded_of h1001)

theorem stmt13_1_7_of_four
    (h1323 : Stmt13_1_2_three) (h1001 : Stmt10_0_1)
    (h3214 : Stmt3_2_14) (h317 : Theorem317Statement)
    : Stmt13_1_7 :=
  stmt13_1_7_of_ten h1323 h1001 h3214 asB56_holds h317 U3.uniqueThreeCaseModelReduction_holds

theorem stmt13_1_7_of_as317
    (h1323 : Stmt13_1_2_three) (h1001 : Stmt10_0_1)
    (h3214 : Stmt3_2_14) (h317 : AS317Sylow)
    : Stmt13_1_7 :=
  stmt13_1_7_of_four h1323 h1001 h3214 (theorem317Statement_of_inputs theoremC58_proved h317)

end CFSG.Quasithin.H13.NQBlock
