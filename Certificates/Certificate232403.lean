module

public import Certificates.Data.Inputs2324QM22
import Certificates.Kernel.C232403.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q CFSG.ComponentClassification.WittDesign in
theorem certificate232403 : m22VEltCheck = true ∧ m22Count (fun g => m22BadB 0 g = true) = 0 ∧
    m22Count (fun g => m22BadB 1 g = true) = 0 ∧ m22Count (fun g => m22BadB 2 g = true) = 0 ∧
    m22VGenCheck = true := KernelC232403.facts232403

end Certificates
