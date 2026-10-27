module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KFourRuData
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueHering

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native in
theorem certificate799202 :
    mcertCheck (ops2fr 28) Blueprint.NativeSporadic.RuSeed1 Blueprint.NativeSporadic.RuSeed2
      CFSG.RankThree.PartTwo.Sec21.Hering214.FourRu.cert = true := KernelMC.fourRuMcert

end Certificates
