module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Check
import Certificates.Kernel.HJ12.X7P3
import CFSG.Certificates.Kernel.HJ12KSound

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12 in
theorem certificate17290 : (hjX7Check = true) ∧ (hjP3Check = true) :=
  ⟨Certificates.Kernel.HJ12K.hjX7Check_of KernelHJ12.ch17290_x7,
    Certificates.Kernel.HJ12K.hjP3Check_of KernelHJ12.ch17290_p3⟩

end Certificates
