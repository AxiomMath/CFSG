module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34OuterDefs
import Certificates.Kernel.L34Outer.Glue
public import Certificates.Data.L34OuterData

public section

namespace Certificates

open CertificateChecks

theorem certificate19768 : CFSG.AGLEmbedding.L34Outer.OuterFacts Certificates.L34Outer.l34OuterData := KernelL34Outer.outerFacts_l34

end Certificates
