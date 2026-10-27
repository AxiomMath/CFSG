module

public import Certificates.Data.CFSGNative.CTIB.Census
public import Certificates.Data.Kernel.BabyMonster.CTIB.OrbitList
import Certificates.Kernel.BabyMonster.Census
import Certificates.Kernel.BabyMonster.QMul

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB in
theorem certificate3099 : (∀ r ∈ Native.censusRecs, Kernel.OrbitList Native.censusAct 2
      (fun v => decide (0 < v) && decide (v < 2 ^ 22)) r.1 r.2)
    ∧ (Native.squaresOK () = true) :=
  ⟨KernelBM.census_orbitLists, KernelBM.squaresOK_true⟩

end Certificates
