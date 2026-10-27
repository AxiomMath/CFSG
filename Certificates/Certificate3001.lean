module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
import Certificates.Kernel.LocalComp.M22Parity

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.WittDesign in
theorem certificate3001 : m22Count (fun g => (∀ x, g (g x) = x) ∧ ∀ x, g x ≠ x) = 0 := KernelLC.m22Count_fpf_invol

end Certificates
