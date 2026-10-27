module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38S1Data
import Certificates.Kernel.U38ProjGen.Checks
import CFSG.Certificates.Kernel.U38ProjGenClosure
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38GenSound
import Certificates.Certificate113

namespace Certificates

open CertificateChecks

public theorem certificate9588 : Subgroup.closure (CFSG.AGLEmbedding.ChevOuter.U38.genSet
    CFSG.AGLEmbedding.ChevOuter.U38.s1Gen) = ⊤ :=
  CFSG.KC.U38PG.closure_genSet_eq_top_of_projGenK KernelU38PG.u38pg9588_check

end Certificates
