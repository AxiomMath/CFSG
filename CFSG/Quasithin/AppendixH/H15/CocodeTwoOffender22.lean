module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffDefs22
public meta import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffDefs22
public import Certificates.Certificate7068
public import Certificates.Certificate490012

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

theorem greedyOff22P :
    ∀ k ∈ [1, 2, 3, 4, 5, 6],
      forallGreedyP pos22s2 inv22s2 (predOff22 k) k [] = true :=
  Certificates.certificate490012

theorem greedyOff22 :
    ∀ k ∈ [1, 2, 3, 4, 5, 6], forallGreedy T22s2.invols (predOff22 k) k [] = true :=
  fun k hk => (forallGreedyP_eq pos22s2_eq (predOff22 k) k []).symm.trans (greedyOff22P k hk)

end CFSG.ASVolI.AppH
