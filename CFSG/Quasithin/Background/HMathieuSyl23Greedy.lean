
module

public import CFSG.Quasithin.Background.HMathieuSyl23
public meta import CFSG.Quasithin.Background.HMathieuSyl23
public import CFSG.Quasithin.Background.HMathieuSyl23Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public import Certificates.Certificate7072

public section

namespace CFSG.Quasithin.H.Mathieu

theorem greedy23P :
    ∀ k ∈ [1, 2, 3, 4, 5],
    forallGreedyP pos23s2 inv23s2 (pred23 k) k [] = true :=
  Certificates.certificate7072

theorem greedy23 :
    ∀ k ∈ [1, 2, 3, 4, 5], forallGreedy T23s2.invols (pred23 k) k [] = true :=
  fun k hk => (forallGreedyP_eq pos23s2_eq (pred23 k) k []).symm.trans (greedy23P k hk)

end CFSG.Quasithin.H.Mathieu
