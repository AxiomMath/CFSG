module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneSporPlaneThData
import Certificates.Kernel.ThCent.Plane31021Glue
import Certificates.Certificate1022
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace Certificates

open CertificateChecks

theorem certificate31021 : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne.thPlaneOK () = true :=
  KernelThList.thPlaneOK_K

end Certificates
