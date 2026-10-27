module

public import CFSG.RankThree.Asc83Table.HeData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.RankThree.Asc83Table.HeData
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
public meta import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8001

public section

namespace CFSG.RankThree.Asc83Table.He

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem he_check :
    mcertCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2 heCert = true :=
  Certificates.certificate8001

end CFSG.RankThree.Asc83Table.He
