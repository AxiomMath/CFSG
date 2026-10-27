module

public import CFSG.OddTranspositions.PartThree.EightSix.OFourMinusCheck
import Certificates.Kernel.MinusQuandle.Checks
import Certificates.Kernel.MinusSecondKind.Checks
import CFSG.Certificates.Kernel.MinusSecondKindSound

public section

namespace Certificates

open CertificateChecks.KernelMinusQ CertificateChecks.KernelMinusSK in
open CFSG.OddTranspositions.PartThree in
theorem certificate1430001 : minusSecondKindCheck () = true :=
  CFSG.KC.MinusSecondKind.secondKind_of rows_ok inv_ok quandle_ok base_ok sk_ok

end Certificates
