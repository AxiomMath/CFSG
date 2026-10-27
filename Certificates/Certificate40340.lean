module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.Fp
import Certificates.Kernel.McertP.Glue
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate40340 : MGen.checkBase (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 j4_23_claims = true ∧
    MGen.checkBase (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 ly_31_claims = true := KernelMP.cert40340

end Certificates
