module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HCheck
import Certificates.Kernel.EvenSporM22.HS08Checks
import Certificates.Kernel.EvenSporM22.HS08ConjChecks
import CFSG.Certificates.Kernel.EvenSporM22.HS08JSound
import CFSG.Certificates.Kernel.EvenSporM22.HS08ConjSound

public section

open CFSG.EvenSporadicStandard.M22Std.HS08Check CFSG.KC.EvenSporM22

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.HS08Check in
theorem certificate26881 : conjCheck = true := by
  have hj := jTabs_eq_jLit KernelEvenSporM22.jOK_jLit
  have h : ConjProp := by
    rw [ConjProp.eq_1, hj]
    exact hs08conjPropJ KernelEvenSporM22.jOK_jLit.2.1 KernelEvenSporM22.hs08jLit_valid
      KernelEvenSporM22.hs08cPairs_length KernelEvenSporM22.hs08cPairs_ok
      KernelEvenSporM22.hs08keys_ok
  exact decide_eq_true h

end Certificates
