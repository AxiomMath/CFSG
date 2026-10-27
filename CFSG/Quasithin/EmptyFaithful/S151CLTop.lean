module

public import CFSG.Quasithin.EmptyFaithful.S151CLRed
public import CFSG.Quasithin.EmptyFaithful.S151CLL2p
public import CFSG.Quasithin.EmptyFaithful.S151CLA6
public import CFSG.Quasithin.EmptyFaithful.S151CLA7
public import CFSG.Quasithin.EmptyFaithful.S151CLL33
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Red
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Loc
public import CFSG.Quasithin.EmptyFaithful.S151CLG2
public import CFSG.Quasithin.EmptyFaithful.S151CLG2D4
public import CFSG.Quasithin.EmptyFaithful.S151CLG2F4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.CLG2

theorem input15120CompList_holds
    (hlist : Lemma115_3_List) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h42 : AsB42)
    (hLJ : Input15120LJ) (hB42 : Input15120B42List) (h118 : TheoremC118) (h126 : TheoremC126)
    (h1416 : StageLemma1416) (h15 : StageLemma1515CE) : Input15120CompList :=
  compList_of_exclusions hlist (compListNoL32_holds hlist h37 h38) (compListNoA6_holds h37 h38)
    (compListNoA7_holds h37 h38) (compListNoG2_holds h38 h42 hLJ h118 h126 h1416 h15)
    (compListNo3D4_holds h38 h42 hLJ h118 h126 h1416 h15)
    (compListNo2F4_holds h38 h42 hLJ hB42 h118 h126 h1416 h15) (compListNoJ4_of_local hB42
        (input15120J4Local_holds h38))
    compListNoL33_holds (compListNoL2p_holds hlist h37 h38)

end CFSG.Quasithin
