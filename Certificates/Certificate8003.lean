module

public import CFSG.RankThree.Asc83Table.RuData
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Ru
  CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint in
theorem certificate8003 :
    mcertCheck (ops2fr 28) NativeSporadic.RuSeed1 NativeSporadic.RuSeed2 ruCert = true := KernelMC.ruMcert

end Certificates
