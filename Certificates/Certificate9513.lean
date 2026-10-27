module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreHeSevenData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.CoreGen.Glue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint in
theorem certificate9513 : coreGenCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2
    CoreHe7.nregs CoreHe7.prog CoreHe7.spec = true := KernelCG.he7Core

end Certificates
