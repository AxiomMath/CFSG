module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HCheck
import Certificates.Kernel.EvenSporM22.HS08Checks
import CFSG.Certificates.Kernel.EvenSporM22.HS08JSound

public section

open CFSG.EvenSporadicStandard.M22Std.HS08Check CFSG.KC.EvenSporM22

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.HS08Check in
theorem certificate26883 : outInvCheck = true := by
  have hj := jTabs_eq_jLit KernelEvenSporM22.jOK_jLit
  have h : OutInvProp := by
    rw [OutInvProp.eq_1, hj]
    exact KernelEvenSporM22.outInvJ_jLit
  exact decide_eq_true h

end Certificates
