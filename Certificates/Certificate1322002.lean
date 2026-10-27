module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenThData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueSporGen3

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.Blueprint CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive in
theorem certificate1322002 : seedCertCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 thLineCert = true := KernelMC.sg3ThCheck

end Certificates
