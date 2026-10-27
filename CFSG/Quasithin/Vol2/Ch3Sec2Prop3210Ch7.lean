module

public import CFSG.Quasithin.Vol2.Ch3Sec2Prop3210Six
public import CFSG.Quasithin.Vol2.Ch7Inputs761

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

theorem stmt3_2_10_four_holds
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Stmt3_2_10_four :=
  fun _ _ _ _ _ _ _ h hV hJ _ hU =>
    Prop3210.not_two_dvd_relIndex (stmt3_2_3_of_a38_a39 h38 h39) stmt3_2_2_eight_proved h hV hJ hU

theorem stmt3_2_10_six_of_stmt3_2_7C (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (h327 : Stmt3_2_7C) : Stmt3_2_10_six :=
  fun _ _ _ _ _ _ _ h hV hJ _ hU hVO hFF g hUg =>
    Prop3210.commutator_eq_bot h323 h3228 h327 h hV hJ hU hVO hFF g hUg

end CFSG.Quasithin.H13
