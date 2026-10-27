module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTitsData
import Certificates.Kernel.TitsOver.L33.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate31072 : CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TitsL33.titsL33Check () = true :=
  KernelTitsOver.L33.check

end Certificates
