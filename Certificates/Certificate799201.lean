module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KFourJ2Data
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueHeringFp

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native in
theorem certificate799201 :
    mcertCheck (opsP 5 14) Blueprint.NativeSporadic.J2Seed1 Blueprint.NativeSporadic.J2Seed2
      CFSG.RankThree.PartTwo.Sec21.Hering214.FourJ2.cert = true := KernelMC.fourJ2Mcert

end Certificates
