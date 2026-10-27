module

public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace Frontier331

theorem stmt3_3_6_of_frontier :
    Stmt3_3_6 :=
  stmt3_3_6_of a38Cat Vol2Native.a39ForSQTKCat_proved VolI.rankTwoA38Types_holds

theorem stmt3_3_8_of_frontier
    (h8one : Stmt3_3_8One) : Stmt3_3_8 :=
  stmt3_3_8_of a38Cat Vol2Native.a39ForSQTKCat_proved B5.asB51_holds h8one

end Frontier331

end CFSG.Quasithin.H13
