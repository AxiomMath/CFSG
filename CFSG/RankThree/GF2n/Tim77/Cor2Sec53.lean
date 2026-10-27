module

public import CFSG.RankThree.GF2n.Tim77.Cor2Rest
public import CFSG.RankThree.GF2n.Tim77.Sec414T
public import CFSG.RankThree.GF2n.Tim77.Sec47
public import CFSG.RankThree.GF2n.Tim77.Sec412

public section

namespace CFSG.RankThree.GF2n.Tim77

theorem tim77Cor2_of_sec53
    (h53 : Tim77Sec53Statement) :
    CFSG.RankThree.GF2n.Stroth80.Tim77Cor2Statement :=
  have h47 : Tim77Sec47Statement := sec47_of
  tim77Cor2_of_rest (sec414t_of h47 (sec412_of h47)) h53

end CFSG.RankThree.GF2n.Tim77
