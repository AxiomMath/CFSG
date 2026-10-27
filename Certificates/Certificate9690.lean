module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftU38Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38GenSound
import Certificates.Kernel.U38ProjGen.Checks
import CFSG.Certificates.Kernel.U38ProjGenClosure
import Certificates.Certificate113

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.ChevOuter.U38 CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.Eight in
public theorem certificate9690 : Subgroup.closure (genSet z8Gen) = ⊤ :=
  CFSG.KC.U38PG.closure_genSet_eq_top_of_projGenK KernelU38PG.u38pg9690_check

end Certificates
