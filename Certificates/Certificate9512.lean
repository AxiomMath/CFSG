module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreHeThreeData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.CoreGen.Glue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint in
theorem certificate9512 : coreGenCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2
    CoreHe3.nregs CoreHe3.prog CoreHe3.spec = true := KernelCG.he3Core

end Certificates
