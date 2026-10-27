module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3RuData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueSporGen3
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenThData

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.Blueprint CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive
  CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis in
theorem certificate1322006 : seedCertCheck (ops2 28) NativeSporadic.RuSeed1 NativeSporadic.RuSeed2 CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.ruCert =
    true := KernelMC.sg3RuCheck

end Certificates
