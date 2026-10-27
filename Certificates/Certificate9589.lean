module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38P1Data
import Certificates.Kernel.U38ProjGen.Checks
import CFSG.Certificates.Kernel.U38ProjGenClosure
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38GenSound
import Certificates.Certificate113

namespace Certificates

open CertificateChecks

public theorem certificate9589 : Subgroup.closure (CFSG.AGLEmbedding.ChevOuter.U38.genSet
    CFSG.AGLEmbedding.ChevOuter.U38.p1Gen) = ⊤ :=
  CFSG.KC.U38PG.closure_genSet_eq_top_of_projGenK KernelU38PG.u38pg9589_check

end Certificates
