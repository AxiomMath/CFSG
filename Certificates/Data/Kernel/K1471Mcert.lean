module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.KC.K1471

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def fusZ (rx ry : Nat) : Word := [(rx, 1), (ry, 1), (rx, 2), (ry, 2)]

@[expose] def fusFacts (rx ry rn on a b k : Nat) : List MFact :=
  [.ord rx 3, .ord ry 3, .ord rn on, .conj rx (fusZ rx ry) (fusZ rx ry),
    .conj ry (fusZ rx ry) (fusZ rx ry),
    .conj rn (fusZ rx ry) ([(rx, a), (ry, b)] ++ (List.replicate k (fusZ rx ry)).flatten),
    .ne (fusZ rx ry) [] 0]

end CFSG.KC.K1471

end
