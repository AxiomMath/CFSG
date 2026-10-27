module

public import CFSG.RankThree.GF2n.Tim77.Cor2Steps
public import CFSG.RankThree.GF2n.Tim77.Sec33
public import CFSG.RankThree.GF2n.Tim77.Sec44
public import CFSG.RankThree.GF2n.Tim77.Sec49
public import CFSG.RankThree.GF2n.Tim77.Sec415b
public import CFSG.RankThree.GF2n.Tim77.Sec415c
public import CFSG.RankThree.GF2n.Tim77.Sec415

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75

theorem tim77Cor2_of_rest
    (h414 : Tim77Sec414Statement) (h53 : Tim77Sec53Statement) :
    CFSG.RankThree.GF2n.Stroth80.Tim77Cor2Statement :=
  have h415a : Tim77Sec415aStatement := sec415a_of h414
  tim77Cor2_of_remaining tim77Sec33_holds sec43_of sec44w_holds
    (sec415_of h415a (sec415b_of h415a tim77Sec49_holds) sec415c_of sec43_of sec44w_holds
      tim77Sec35_holds) h53

end CFSG.RankThree.GF2n.Tim77
