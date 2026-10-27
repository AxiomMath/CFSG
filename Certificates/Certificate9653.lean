module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreJ4ThreeData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.CoreGen.Glue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint in
theorem certificate9653 : coreGenCheck (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2
    CoreJ43.nregs CoreJ43.prog CoreJ43.spec = true := KernelCG.j4Core

end Certificates
