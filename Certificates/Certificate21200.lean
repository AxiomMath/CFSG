module

public import CFSG.LargeExtraspecial.AS35YRU33Data
import CFSG.Certificates.Kernel.PermCent.U33Sound
import Certificates.Kernel.PermCent.K21200

public section

open CFSG.Certificates.Kernel.PkCV.U33T

namespace Certificates

open CertificateChecks

theorem certificate21200 : CFSG.LargeExtraspecial.AS35YR.u33InvConjCheck = true := by
  rw [invConj_eq]
  exact KernelPermCent.k21200

end Certificates
