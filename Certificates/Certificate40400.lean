module

public import CFSG.RankThree.PartTwo.Sec13.K135ONData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueON

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
  CFSG.RankThree.PartTwo.Sec13.F135Last.K135 in
theorem certificate40400 :
    mcertCheck (opsP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 onCert = true := KernelMC.k135ONMcert

end Certificates
