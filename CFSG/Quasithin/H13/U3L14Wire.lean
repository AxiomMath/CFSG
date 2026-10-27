module

public import CFSG.Quasithin.H13.U3L14D8
public import CFSG.Quasithin.H13.NQBlockXiMinus
public import CFSG.Quasithin.EmptyFaithful.S152HeProp134
public import CFSG.Quasithin.Vol2.GoldschmidtTDLem141Holds
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ9

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt13_3_14d_holds
    (h1332 : Stmt13_3_2) (h1336 : A6.Stmt13_3_6) : Stmt13_3_14d :=
  stmt13_3_14d_of h1332 h1336 (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
    (a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved))
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) CFSG.Quasithin.prop134E9He_holds
    Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved
    (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
    (NQBlock.input3213_of_316 Ch3T316W.theorem316Statement_holds) NQCore.input137_holds
    Vol2.Ch10.tmp1_4_1_four_proved Ch3T316W.theorem316Statement_holds

theorem stmt13_3_14_holds
    (h1332 : Stmt13_3_2) (h1336 : A6.Stmt13_3_6) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (hF : A318Facts) (h1310 : Stmt13_3_10) (hd : Stmt13_3_14d)
    (hA6 : Set14ProducerA6) (hL32 : Set14ProducerL32) (hU33 : Set14ProducerU33) :
    A6.Stmt13_3_14 :=
  stmt13_3_14_of h1332 h1336 (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
    (a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved))
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) hC58 h317 h56 hF h1310 hd hA6 hL32 hU33

end CFSG.Quasithin.H13.U3
