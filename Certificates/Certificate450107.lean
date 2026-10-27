module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocksCheck
import Certificates.Kernel.Sporadic.Fi22.B450107

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB in
theorem certificate450107 : checkBlocks () = true :=
  KernelSpor.B450107.check

end Certificates
