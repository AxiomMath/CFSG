module

public import CFSG.RankThree.Asc83Table.RuData
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.RankThree.Asc83Table.RuData
public meta import Certificates.Data.CFSGNative.SectionRank.F2Fast
public meta import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8003

public section

namespace CFSG.RankThree.Asc83Table.Ru

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem ru_check :
    mcertCheck (ops2fr 28) NativeSporadic.RuSeed1 NativeSporadic.RuSeed2 ruCert = true :=
  Certificates.certificate8003

end CFSG.RankThree.Asc83Table.Ru
