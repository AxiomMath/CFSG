module

public import CFSG.Quasithin.EmptyFaithful.T1521SReduce
public import CFSG.Quasithin.EmptyFaithful.T1521SSzMain
public import CFSG.Quasithin.EmptyFaithful.T1521SL2EAll
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkFinal
public import CFSG.Quasithin.EmptyFaithful.T1521SA5L2
public import CFSG.Quasithin.EmptyFaithful.T1521SA5Blk
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4All
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Aut
public import CFSG.Quasithin.EmptyFaithful.T1521SL3CMain
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Main
public import CFSG.Quasithin.EmptyFaithful.T1521SCutBlock
public import CFSG.Quasithin.EmptyFaithful.T1521SCutComp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem struct15121_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Struct15121 :=
  struct15121_of h37 h38 typeCutBlock1521 typeCutComp1521 dich1521BlockL2_holds
    (dich1521BlockA5_of_orbits fun _ _ _ => a3Orbits_of_a37_a38 h37 h38)
    (dich1521L2_of_two_of_ge_three
      (dich1521L2_two_of_orbits fun _ _ _ => a3Orbits_of_a37_a38 h37 h38)
      fun G _ _ X S L hStd hco hZ hn =>
        Or.inl (dich1521L2_big_of h37 h38 G X S L hStd hco hZ hn))
    (dich1521Sz_of h37 h38) (dich1521U3_of (nrm1521U3_of h37 h38))
    (dich1521L3_of_parts (e1L3_of h37 h38) (e1L3Cover_of h37 h38) autFactL3_holds)
    (dich1521Sp4_of_orbits h37 h38)

end CFSG.Quasithin
