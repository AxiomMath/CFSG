module

public import Certificates.Certificate3099

public section

namespace CFSG.Monster.B.CTIB

theorem census_orbitLists : ∀ r ∈ Native.censusRecs,
    Kernel.OrbitList Native.censusAct 2 (fun v => decide (0 < v) && decide (v < 2 ^ 22)) r.1 r.2 :=
  Certificates.certificate3099.1

theorem squaresOK_eq_true : Native.squaresOK () = true :=
  Certificates.certificate3099.2

end CFSG.Monster.B.CTIB
