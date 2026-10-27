module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310Y
public import CFSG.Quasithin.Vol2.KGFactMinParHe
public import CFSG.Quasithin.Vol2.KGFactMinParLn2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3

theorem claim8310Excl_of_kg
    (hE22 : E2.E22StatementC) (h443 : Stmt4_4_3Orbit') (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h3228 : Stmt3_2_2_eight) (hC58 : TheoremC58) (h317 : AS317Sylow) (h326 : Stmt3_2_6C)
    (h3108 : Stmt3_2_10_eight) : Claim8310Excl :=
  claim8310Excl_of hE22 h443 h37 h38 h39 h3228 hC58 h317 h326 h3108
    KGMinPar.kg8310MinParLn2_holds KGMinPar.kg8310MinParHe_holds

theorem stmt8_3_10_of_kg
    (hE22 : E2.E22StatementC) (h443 : Stmt4_4_3Orbit') (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h3228 : Stmt3_2_2_eight) (hC58 : TheoremC58) (h317 : AS317Sylow) (h332 : Stmt3_3_2MTwo)
    (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight) (h832 : Stmt8_3_2) (h835 : Stmt8_3_5)
    (h837 : Stmt8_3_7) (h839 : Stmt8_3_9) (hGzC : Claim8310Gz) (hNC : Claim8310N) :
    Stmt8_3_10 :=
  stmt8_3_10_of h3228 (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38) (a39ForSQTK_of_cat h39)
    hC58 h317 h332 h326 h832 h835 h837 h839
    (claim8310Excl_of_kg hE22 h443 h37 h38 h39 h3228 hC58 h317 h326 h3108) hGzC hNC

end CFSG.Quasithin.H13
