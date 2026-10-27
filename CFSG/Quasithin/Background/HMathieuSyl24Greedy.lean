
module

public import CFSG.Quasithin.Background.HMathieuSyl24GreedyBase

public import CFSG.Quasithin.Background.HMathieuSyl24
public meta import CFSG.Quasithin.Background.HMathieuSyl24
public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll
public import Certificates.Certificate7075

public section

namespace CFSG.Quasithin.H.Mathieu

theorem greedy24All :
    forallGreedyAll pos24s2 inv24s2 pred24 7 [] = true :=
  Certificates.certificate7075

theorem greedy24 {k : ℕ} (hk : k ≤ 7)
    :
    forallGreedy T24s2.invols pred24 k [] = true :=
  (forallGreedyP_eq pos24s2_eq pred24 k []).symm.trans (forallGreedyAll_le 7 [] greedy24All k hk)

end CFSG.Quasithin.H.Mathieu
