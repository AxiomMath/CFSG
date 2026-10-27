module

public import CFSG.RankThree.PartTwo.KFacts.HeringKS12J3Data
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueHering

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native in
theorem certificate799010 :
    mcertCheck (ops2fr 80) Blueprint.NativeSporadic.J3Seed1 Blueprint.NativeSporadic.J3Seed2
      CFSG.RankThree.PartTwo.KFacts.KS12J3.cert = true := KernelMC.ks12J3Mcert

end Certificates
