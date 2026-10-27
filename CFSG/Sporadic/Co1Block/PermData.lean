module

public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Monster.B.Co2.Native

abbrev certDeg : Nat := 98280

@[expose] def certVecHex : String := include_str "Data"/"Vecs.txt"

@[expose, irreducible] def certActHex : String := include_str "Data"/"Acts.txt"

@[expose, irreducible] def certVecs : Array Nat := hexTable 6 98280 0 certVecHex

@[expose, irreducible] def certAct (k : Nat) : Array Nat := hexTable 5 98280 (98280 * k) certActHex

@[expose] def certBasisIdx : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 26]

end CFSG.Sporadic.Co1Block
