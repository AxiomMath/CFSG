module

public import Certificates.Data.Y63.Spec
import Certificates.Kernel.Y63.C1
import Certificates.Kernel.Y63.C2
import Certificates.Kernel.Y63.Q01
import Certificates.Kernel.Y63.Q23
import Mathlib.Tactic.IntervalCases

public section

namespace Certificates

open CertificateChecks.KernelY63

open CFSG.OddStandard.HigherRank.YamadaG23 in
theorem certificate441836 : ∃ D : Y63Chk.Data, D.Spec :=
  ⟨dK, tab, word, mul, inv, mspec, sspec, fun k hk => by
    interval_cases k
    · exact q0
    · exact q1
    · exact q2
    · exact q3⟩

end Certificates
