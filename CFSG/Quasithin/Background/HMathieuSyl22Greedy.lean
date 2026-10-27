
module

public import CFSG.Quasithin.Background.HMathieuSyl22GreedyBase

public import CFSG.Quasithin.Background.HMathieuSyl22
public meta import CFSG.Quasithin.Background.HMathieuSyl22
public import CFSG.Quasithin.Background.HMathieuSyl22Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public import Certificates.Certificate7069
public import Certificates.Certificate7075Base
public import Certificates.Kernel.HMathieu.C7075

public section

namespace CFSG.Quasithin.H.Mathieu

theorem greedy22P :
    ∀ k ∈ [1, 2, 3, 4, 5, 6],
    forallGreedyP pos22s2 inv22s2 (pred22 k) k [] = true :=
  Certificates.certificate7069

theorem greedy22 :
    ∀ k ∈ [1, 2, 3, 4, 5, 6], forallGreedy T22s2.invols (pred22 k) k [] = true :=
  fun k hk => (forallGreedyP_eq pos22s2_eq (pred22 k) k []).symm.trans (greedy22P k hk)

end CFSG.Quasithin.H.Mathieu
