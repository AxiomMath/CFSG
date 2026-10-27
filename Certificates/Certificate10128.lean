module

public import CFSG.RankThree.PartOne.KS.HeSevenDihedralDefs
import Certificates.Kernel.HeLoc.DihKGlue

public section

namespace Certificates

open CFSG.RankThree.PartOne in
theorem certificate10128 : heSevenDihedralOK () = true :=
  CertificateChecks.KernelHeLoc.Seven.heSevenDihedralOK_of

end Certificates
