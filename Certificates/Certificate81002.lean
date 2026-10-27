module

public import Certificates.Data.E8TenTwo
import Certificates.Kernel.E8TenTwo.Codes
import Certificates.Kernel.E8TenTwo.Cover
import Certificates.Kernel.E8TenTwo.Link
import Certificates.Kernel.E8TenTwo.Side
import CFSG.Certificates.Kernel.E8TenTwoBitsSound

public section

namespace Certificates

open CertificateChecks

theorem certificate81002 : E8TenTwo.e8TenTwoCheck () = true :=
  CFSG.KC.E8TenTwoBits.e8TenTwoCheck_of KernelE8TenTwo.ratOk_true KernelE8TenTwo.colsOk_true
    KernelE8TenTwo.wordsOk_true KernelE8TenTwo.bfsOk_true KernelE8TenTwo.coverOK_bits
    KernelE8TenTwo.factOK_bits KernelE8TenTwo.codesOK_bits

end Certificates
