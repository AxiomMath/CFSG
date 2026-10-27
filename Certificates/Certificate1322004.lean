module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3J2Data
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueSporGen3
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenThData

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.Blueprint CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive
  CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis in
theorem certificate1322004 : seedCertCheck (opsP 5 14) NativeSporadic.J2Seed1 NativeSporadic.J2Seed2 j2Cert =
    true := KernelMC.sg3J2Check

end Certificates
