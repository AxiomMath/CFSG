module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi22E16Inputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi22E16Inputs
import Certificates.Kernel.Sporadic.Fi22.E16Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.YS14 in
theorem certificate27754 : fi22E16Check () = true :=
  KernelSpor.Fi22E16.fi22E16Check_true

end Certificates
