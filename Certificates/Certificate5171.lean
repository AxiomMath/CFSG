module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCTitsInputs
import Certificates.Kernel.SporSch.Tits.WC5171

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree in
theorem certificate5171 : titsWCCheck = true :=
  KernelSporSch.TitsWC5171.titsWC_true

end Certificates
