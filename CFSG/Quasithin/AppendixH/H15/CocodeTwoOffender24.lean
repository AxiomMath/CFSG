module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffDefs24
public meta import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffDefs24
public import Certificates.Certificate7074
public import Certificates.Certificate490011

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

theorem greedyOff24All :
    forallGreedyAll pos24s2 inv24s2 predOff24 7 [] = true :=
  Certificates.certificate490011

theorem greedyOff24 {k : ℕ}
    (hk : k ≤ 7) :
    forallGreedy T24s2.invols predOff24 k [] = true :=
  (forallGreedyP_eq pos24s2_eq predOff24 k []).symm.trans
    (forallGreedyAll_le 7 [] greedyOff24All k hk)

end CFSG.ASVolI.AppH
