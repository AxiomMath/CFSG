module

public import Certificates.Certificate6014

public section

namespace CFSG.Monster.AxisCount.HS

theorem rec_ok_4 :
    ∀ s ∈ recShard_4, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  Certificates.certificate6014

end CFSG.Monster.AxisCount.HS
