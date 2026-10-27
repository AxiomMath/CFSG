module

public import CFSG.RankThree.Asc83Table.J3Data
public import Certificates.Data.CFSGNative.J3.Data
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.RankThree.Asc83Table.J3Data
public meta import Certificates.Data.CFSGNative.J3.Data
public meta import Certificates.Data.CFSGNative.SectionRank.F2Fast
public meta import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8004

public section

namespace CFSG.RankThree.Asc83Table.J3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem j3_check :
    j3Check NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 CFSG.Sporadic.J3.Native.j3Data.pts
      CFSG.Sporadic.J3.Native.j3Data.n j3Cert = true :=
  Certificates.certificate8004

end CFSG.RankThree.Asc83Table.J3
