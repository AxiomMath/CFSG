module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.SquareCheck
import Certificates.Kernel.Co3Square.Glue

public section

namespace Certificates

theorem certificate25000 : CFSG.EvenSporadicStandard.Co3Std.co3SquareCheck = true :=
  CertificateChecks.KernelCo3Square.co3SquareCheck_true

end Certificates
