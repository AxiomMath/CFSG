module

public import Certificates.Data.CFSGNative.J4Tree.Aff
public import CFSG.Sporadic.J4.QTNative
public import CFSG.Sporadic.J4.QTRankData

public section

namespace CFSG.ASVolI

open CFSG.J4Tree.Native CFSG.Sporadic.J4.QT

@[expose] def burnsideJ4NP_affDataOK (_ : Unit := ()) : Bool :=
  (List.range 11).all (fun j => codeOfWord (uWord j) == uCode[j]?.getD 1) &&
    (List.range 4).all fun i => codeOfWord (kWords.getD i []) == kCode[i]?.getD 1

end CFSG.ASVolI
