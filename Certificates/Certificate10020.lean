module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalNative
import Certificates.Kernel.J2Cover.EncTab
import Certificates.Kernel.J2Cover.EncM22

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.J2Cover.External in
theorem certificate10020 :
    (chainCheck = true)
    ∧ (tableCheck = true)
    ∧ (elemCheck = true)
    ∧ (lamCheck = true) :=
  ⟨KernelJ2Cover.chainC, KernelJ2Cover.tableCE, KernelJ2Cover.elemCE, KernelJ2Cover.lamCE⟩

end Certificates
