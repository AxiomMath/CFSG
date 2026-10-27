module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3HeData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueSporGen3
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenThData

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.Blueprint CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive
  CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis in
theorem certificate1322005 : seedCertCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2 CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.heCert =
    true := KernelMC.sg3HeCheck

end Certificates
