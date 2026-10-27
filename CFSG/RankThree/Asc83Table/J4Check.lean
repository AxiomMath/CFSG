module

public import CFSG.RankThree.Asc83Table.J4Data
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.RankThree.Asc83Table.J4Data
public meta import Certificates.Data.CFSGNative.SectionRank.F2Fast
public meta import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8002

public section

namespace CFSG.RankThree.Asc83Table.J4

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem j4_check :
    mcertCheck (ops2fr 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 j4Cert = true :=
  Certificates.certificate8002

end CFSG.RankThree.Asc83Table.J4
