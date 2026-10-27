module

public import Certificates.Data.CFSGNative.J4.Data

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

@[expose] def kWords : List (List Int) :=
  ["ccA", "BCccBBCccBBCccBBCccBBCccB", "abaccCabaccCabaccCabaccCabaccCabaccCabaccC",
    "AbcBAbcBAbcBAbcBAbcBAbcBAbcB"].map lettersOfString

@[expose] def pcSeqs : List (List Nat) :=
  [[0], [0, 1, 0], [0, 0], [0, 0, 1, 0, 0], [0, 2, 0], [3], [3, 1, 3], [2], [2, 1, 2], [1]]

end CFSG.Sporadic.J4.QT
