module

public import CFSG.RankThree.Asc83Table.HSData
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.RankThree.Asc83Table.HSData
public meta import Certificates.Data.CFSGNative.SectionRank.F2Fast
public meta import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8000

public section

namespace CFSG.RankThree.Asc83Table.HS

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem hs_check :
    mcertCheck (ops2fr 20) NativeSporadic.HSSeed1 NativeSporadic.HSSeed2 hsCert = true :=
  Certificates.certificate8000

end CFSG.RankThree.Asc83Table.HS
