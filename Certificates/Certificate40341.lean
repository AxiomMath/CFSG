module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData2
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.Fp
import Certificates.Kernel.McertP.ONGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate40341 : PClaim.check (opsP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 on_31_claims = true ∧
    PClaim.check (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 th_31_claims = true ∧
    OClaim.check (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 th_ord4_claims = true := KernelMP.cert40341

end Certificates
