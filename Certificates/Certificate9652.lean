module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreThFiveData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.CoreGen.Glue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint in
theorem certificate9652 : coreGenCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2
    CoreTh5.nregs CoreTh5.prog CoreTh5.spec = true := KernelCG.thCore

end Certificates
