module

public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Cl

public section

namespace CFSG.HardMathSupport.Dickson.I271.RkBMFi24Inv

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi24.Native Timmesfeld.Fi24Cl

set_option compiler.extract_closed false

@[expose] def repWordsN : Array (List Nat) :=
  #[[18], [16, 19], [14, 16, 16, 14, 16, 16], [16], [2]]

@[expose] def invData : Array (List Nat × List Nat × List Nat) := #[
  ([17, 25, 20, 13, 13, 14, 25, 14, 21, 8, 8, 23, 24, 16, 8, 6, 4, 17, 13, 14],
    [25, 16, 18, 21, 23, 14, 16, 23, 15, 8, 18, 8, 19, 14, 4, 8, 15, 13, 19, 12, 0, 10, 4, 17, 12],
    [20, 14, 17, 20, 18, 14, 8, 15, 8, 10, 12, 9, 6, 5, 15, 8, 7, 0, 10, 12, 21, 4]),
  ([20, 23, 14, 16, 18, 25, 12, 11, 13, 18, 22, 5, 20, 7, 4, 24, 2, 18, 9, 24, 14],
    [24, 16, 20, 17, 15, 25, 17, 15, 19, 8, 25, 13, 11, 22, 17, 4, 21, 12, 10, 7, 2, 0, 22, 25, 4],
    [24, 18, 20, 12, 23, 14, 18, 13, 8, 8, 11, 12, 8, 10, 5, 14, 14, 24, 0, 3, 7, 7, 15]),
  ([24, 16, 24, 17, 12, 15, 15, 19, 14, 24, 21, 8, 10, 21, 24, 15, 12, 6, 8, 24, 5, 6],
    [25, 21, 23, 21, 15, 17, 12, 12, 15, 9, 10, 22, 8, 24],
    [24, 20, 23, 12, 15, 12, 25, 18, 9, 15, 20, 19, 15, 4, 7, 8, 4, 23]),
  ([24, 20, 19, 21, 15, 22, 14, 20, 23, 8, 8, 19, 8, 21, 4, 23, 20, 4, 24, 0, 3, 23, 12, 11],
    [25, 16, 21, 16, 14, 13, 20, 14, 14, 19, 10, 22, 15, 10, 15],
    [25, 20, 18, 14, 19, 25, 15, 13, 8, 19, 11, 12, 10, 6, 8, 14, 7, 3, 12, 23, 18, 0]),
  ([22, 21, 13, 17, 14, 20, 14, 20, 8, 12, 8, 11, 9, 5, 7, 23, 17, 4, 0, 4, 8, 22, 11],
    [25, 16, 20, 25, 20, 13, 15, 19, 15, 12, 25, 8, 25, 8, 12, 25, 5, 16, 10, 21, 14, 0, 7, 15, 0,
      6],
    [19, 12, 15, 15, 12, 12, 11, 19, 11, 14, 13, 5, 16, 9, 9, 16, 2, 4, 12, 19, 15])]

@[expose] def eqOnBase (L : Array Table) (u v : List Nat) : Bool :=
  chainBase.all fun b => apWord L u b == apWord L v b

@[expose] def invAt (L : Array Table) (r s t t' : List Nat) : Bool :=
  (s ++ t ++ t').all (· < 26) &&
  eqOnBase L (s ++ s) [] && eqOnBase L (s ++ r ++ s) (invWord r) &&
  eqOnBase L (t ++ t) [] && eqOnBase L (t' ++ t') [] &&
  eqOnBase L (t ++ r) (r ++ t) && eqOnBase L (t' ++ r) (r ++ t') &&
  eqOnBase L (t ++ t' ++ t ++ t' ++ t ++ t') [] && !eqOnBase L (t ++ t') []

@[expose] def invAtRep (L : Array Table) (i : Nat) : Bool :=
  invAt L repWordsN[i]! invData[i]!.1 invData[i]!.2.1 invData[i]!.2.2

@[expose] def invCheck (O : Enum) : Bool :=
  let L := chainLetters O
  invAtRep L 0 && invAtRep L 1 && invAtRep L 2 && invAtRep L 3 && invAtRep L 4

end CFSG.HardMathSupport.Dickson.I271.RkBMFi24Inv
