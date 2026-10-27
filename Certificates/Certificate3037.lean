
module


public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
import Certificates.Kernel.Sporadic.Fi22.F1Model

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native in
theorem certificate3037 : fi22GraphOuterHex.length = 3 * 3510 ∧
      isInvA 3510 fi22GraphOuterArr (invCand 3510 fi22GraphOuterArr) = true := KernelSpor.Fi22F1M.facts3037

end Certificates
