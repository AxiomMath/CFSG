module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3J4Data
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueSporGen3
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenThData

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.Blueprint CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive
  CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis in
theorem certificate1322007 : seedCertCheck (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.j4Cert =
    true := KernelMC.sg3J4Check

end Certificates
