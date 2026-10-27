module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2InvertsGenNative
import Certificates.Kernel.J2Cover.Ivg17264Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact in
theorem certificate17264 : ivgCheck = true :=
  KernelJ2Cover.KF17260.ivg

end Certificates
