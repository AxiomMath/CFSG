module

public import Certificates.Certificate6017

public section

namespace CFSG.Monster.AxisCount.HS

theorem rec_ok_7 :
    ∀ s ∈ recShard_7, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  Certificates.certificate6017

end CFSG.Monster.AxisCount.HS
