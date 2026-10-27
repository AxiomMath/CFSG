module

public import CFSG.Quasithin.H13.A5Close1321
public import CFSG.Quasithin.H13.A5M22HatRow
public import CFSG.Quasithin.H13.A5M12Row
public import CFSG.Quasithin.H13.KGFactJ2Row
public import CFSG.Quasithin.H13.KGLieNatSU
public import CFSG.Quasithin.H13.KGLieSp4Four
public import CFSG.Quasithin.H13.KGLieG2
public import CFSG.Quasithin.H13.KGLieG2Four
public import CFSG.Quasithin.H13.KGLieTwSL2
public import CFSG.Quasithin.H13.KGLieTwNine
public import CFSG.Quasithin.H13.KGLieTwNineTwo
public import CFSG.Quasithin.H13.KGLieTwTwist
public import CFSG.Quasithin.H13.A5Triple
public import CFSG.Quasithin.H13.A5L5Ten
public import CFSG.Quasithin.H13.A5S136d
public import CFSG.Quasithin.H13.A5S136n
public import CFSG.Quasithin.H13.A5S136o
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem facts1321_of_b45
    (b45 : AsB45) : Facts1321 :=
  ⟨b45, H.Mathieu.stmtH14_4, A5.factLieRows1321_of KGLie.factLieSL2Row1321_holds
      KGLie.factLieSL3Row1321_holds KGLie.factLieSL3FourRow1321_holds KGLie.factLieSp4Row1321_holds
      KGLie.factLieSp4FourRow1321_holds KGLie.factLieG2Row1321_holds
      KGLie.factLieG2FourRow1321_holds KGLie.factLieOrthRow1321_holds
      KGLie.factLieOrthFourRow1321_holds KGLie.factLieSU3Row1321_holds KGLie.factLieSzRow1321_holds
      KGLie.factLieNineRow1321_holds KGLie.factLieNineTwoRow1321_holds
      KGLie.factLieNineFourRow1321_holds KGLie.factLieTwistRow1321_holds
      KGLie.factLieTwistTwoRow1321_holds KGLie.factLieTwistFourRow1321_holds, factM12Row1321_holds,
    factM22HatRow1321_holds, factJ2Row1321_holds, factA5Rows1321, factSymRows1321,
    factA7FourRow1321, factTripleA6Row1321, factLNatRow1321, factL5TenRow1321⟩

theorem a38ForSQTKCat_holds
    : Vol2Native.A38ForSQTKCat :=
  Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
    Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved

theorem input13518_of_b45
    (h1323 : Input1323Two) (h1326 : Input1326Two) (h1336 : Input1336) (b45 : AsB45) :
    Input13518 :=
  input13518_of_facts h1323 h1326 h1336 VolI.stmtF956i (a38ForSQTK_of_cat a38ForSQTKCat_holds)
    (facts1321_of_b45 b45) factA7Grp1321 factL3Grp1321

theorem end136_of_fin
    (h1323 : Input1323Two) (h1336 : Input1336) (h1338 : A6.Stmt13_3_8) (hfin : Fin136) :
    End136 :=
  end136_of h1323 h1336 h1338 Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds hfin

theorem elim1366CD_holds
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) : Elim1366CD :=
  elim1366CD h1222 h517 Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds

theorem elim1366EF_of_facts
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (hL33 : FactConfL33) (hL2 : FactConfL2)
    (hSp : FactConfSpor) : Elim1366EF :=
  elim1366EF_of h1222 h517 Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds hL33 hL2 hSp

end CFSG.Quasithin.H13.A5
