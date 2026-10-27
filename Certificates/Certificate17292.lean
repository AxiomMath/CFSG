module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Check
import Certificates.Kernel.HJ12.T1
import CFSG.Certificates.Kernel.HJ12KTSound

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12 in
theorem certificate17292 : (hjTauCheck = true) ∧ (hjT1Check = true) :=
  ⟨Certificates.Kernel.HJ12K.hjTauCheck_of KernelHJ12.ch17292_tau,
    Certificates.Kernel.HJ12K.hjT1Check_of KernelHJ12.ch17292_t1⟩

end Certificates
