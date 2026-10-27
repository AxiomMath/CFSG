module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelNative
import Certificates.Kernel.J2Cover.EncClass

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.J2Cover.Kernel in
theorem certificate10021 :
    (cpACheck = true)
    ∧ (crACheck = true)
    ∧ (cpTCheck = true)
    ∧ (crTCheck = true)
    ∧ (crUCheck = true) :=
  KernelJ2Cover.facts10021E

end Certificates
