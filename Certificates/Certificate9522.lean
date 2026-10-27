module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeInputs
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint in
theorem certificate9522 : tzCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2
    thThreeN thThreeProg thTzSpec = true := KernelMC.thTz

end Certificates
