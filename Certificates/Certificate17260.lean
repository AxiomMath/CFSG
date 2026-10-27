module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFactNative
import Certificates.Kernel.J2Cover.KFact17260Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact in
theorem certificate17260 : (kf2Check = true) ∧ (y0Check = true) ∧ (p3Check = true) :=
  KernelJ2Cover.KF17260.facts17260

end Certificates
