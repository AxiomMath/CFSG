module

public import CFSG.RankThree.Asc83Table.J3Data
public import Certificates.Data.CFSGNative.J3.Data
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.J3Local.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.J3
  CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint in
theorem certificate8004 :
    j3Check NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 CFSG.Sporadic.J3.Native.j3Data.pts
      CFSG.Sporadic.J3.Native.j3Data.n j3Cert = true := KernelJ3L.j3_check_K

end Certificates
