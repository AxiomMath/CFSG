module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreFi24SevenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreSplit
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.F24Core.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint in
theorem certificate9655 : partCheck (ops3 781) NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2
    CoreFi247.nregs CoreFi247.prog CoreFi247.spec CoreFi247.cutA CoreFi247.cutB = true := KernelMC.F24C.part2

end Certificates
