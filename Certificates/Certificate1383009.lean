module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.LocalCheck
import Certificates.Kernel.MinusDerived.A5Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.OddTranspositions.PartThree in
theorem certificate1383009 : minusLocalCheck () = true :=
  KernelMinusA5.localCheck

end Certificates
