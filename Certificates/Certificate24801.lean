module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
import Certificates.Kernel.Co2Chain.M22Beta24801

public section

namespace Certificates

open CFSG.EvenSporadicStandard.M22Std.OutCheck in
theorem certificate24801 : CFSG.ComponentClassification.RankTwoSporadic.M22.autA betaArr = true :=
  CertificateChecks.KernelCo2Chain.M22Beta.check

end Certificates
