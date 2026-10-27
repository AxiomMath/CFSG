module

public import CFSG.RankThree.Asc83Table.J4Data
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.J4
  CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint in
theorem certificate8002 :
    mcertCheck (ops2fr 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 j4Cert = true := KernelMC.j4Mcert

end Certificates
