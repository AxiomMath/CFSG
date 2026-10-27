module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12ThreeThreeCheck
import Certificates.Kernel.HJ12.ThreeThree
import CFSG.Certificates.Kernel.HJ12KTSound

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12 in
theorem certificate17283 : hjThreeThreeCheck () = true :=
  Certificates.Kernel.HJ12K.hjThreeThreeCheck_of KernelHJ12.ch17283_z KernelHJ12.ch17283_tri
    KernelHJ12.ch17283_a1 KernelHJ12.ch17283_a2

end Certificates
