module

public import CFSG.RankThree.Asc83Table.HeData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.He
  CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint in
theorem certificate8001 :
    mcertCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2 heCert = true := KernelMC.heMcert

end Certificates
