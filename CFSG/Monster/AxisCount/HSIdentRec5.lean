module

public import Certificates.Certificate6015

public section

namespace CFSG.Monster.AxisCount.HS

theorem rec_ok_5 :
    ∀ s ∈ recShard_5, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  Certificates.certificate6015

end CFSG.Monster.AxisCount.HS
