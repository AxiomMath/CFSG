module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalGenURuData
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.F2
import Certificates.Kernel.MatCert.GlueRuGenU

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate42304 : MGenU.check (ops2 28) NativeSporadic.RuSeed1 NativeSporadic.RuSeed2 ru_7_genu = true :=
  KernelMC.ruGenU

end Certificates
