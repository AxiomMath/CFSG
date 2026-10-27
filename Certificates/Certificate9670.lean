module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Y9Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38GenSound
import Certificates.Kernel.U38ProjGen.Checks
import CFSG.Certificates.Kernel.U38ProjGenClosure
public import Certificates.Certificate113

namespace Certificates

open CertificateChecks

public theorem certificate9670 : Subgroup.closure (CFSG.AGLEmbedding.ChevOuter.U38.genSet
    CFSG.AGLEmbedding.ChevOuter.U38.y9Gen) = ⊤ :=
  CFSG.KC.U38PG.closure_genSet_eq_top_of_projGenK KernelU38PG.u38pg9670_check

end Certificates
