module

public import CFSG.RankThree.PartTwo.KFacts.HeringKS12ONData
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueON

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native in
theorem certificate799020 :
    mcertCheck (ops3 154) Blueprint.NativeSporadic.ONSeed1 Blueprint.NativeSporadic.ONSeed2
      CFSG.RankThree.PartTwo.KFacts.KS12ON.cert = true := KernelMC.ks12ONMcert

end Certificates
