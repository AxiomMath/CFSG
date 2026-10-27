module

public import Certificates.Certificate6012

public section

namespace CFSG.Monster.AxisCount.HS

theorem rec_ok_2 :
    ∀ s ∈ recShard_2, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  Certificates.certificate6012

end CFSG.Monster.AxisCount.HS
