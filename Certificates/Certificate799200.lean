module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KFourHeData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueHeringFp

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native in
theorem certificate799200 :
    mcertCheck (opsP 7 50) Blueprint.NativeSporadic.HeSeed1 Blueprint.NativeSporadic.HeSeed2
      CFSG.RankThree.PartTwo.Sec21.Hering214.FourHe.cert = true := KernelMC.fourHeMcert

end Certificates
