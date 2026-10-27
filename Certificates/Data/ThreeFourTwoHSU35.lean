module

public import Certificates.Data.HSFiveU35Data
public import Certificates.Data.HNUnitaryBridge

public section

namespace Certificates.ThreeFourTwoHSU35

open CFSG.PSL3Four.Native

@[expose] def hsU35Labels : Array Nat :=
  #[0, 45, 70, 72, 82, 55, 28, 16, 35, 87, 73, 48, 74, 11, 64, 84, 57, 61, 8, 68, 34, 69, 63, 77,
    42, 53, 46, 40, 14, 78, 94, 41, 86, 9, 33, 32, 18, 49, 23, 98, 15, 83, 56, 60, 22, 4, 93, 89,
    2, 5]

@[expose] def hsU35GenWords : List (List Int) :=
  [[-2, 1, 1, -2, 1, -2, 1, 1, 2, -1, -1, -2, -1, 2, 1, -2],
   [-2, 1, 1, 1, 2, 1, 1, -2, -1, 2, 1, -2, 1, 1, 1, 1, 2, 1, 1, -2],
   [-1, -2, 1, 1, 1, 1, -2, 1, 1, -2, -1, -1, 2, 1, -2, -1, 2, 1],
   [-2, 1, 2, 1, -2, 1, 1, 1, 1, 2, -1, -2, -1, -2, -1, -2, 1, 1, 2, -1, -1, -1, 2, -1, 2, -1,
    -1, 2],
   [-1, -2, 1, 2, -1, 2, 1, 1, 1, -2, -1, -1, -1, -1, 2],
   [-1, -2, 1, -2, -1, 2, 1, 2, 1, 1, -2, -1, -1, 2, 1, 1, 1, 1, 2]]

@[expose] def labelsOK (_ : Unit := ()) : Bool :=
  hsU35Labels.size == 50 && (allBelow 50 fun i => decide (hsU35Labels[i]! < 100)) &&
    allBelow 50 fun i => allBelow 50 fun j => i == j || hsU35Labels[i]! != hsU35Labels[j]!

@[expose] def actsOK (k : Nat) : Bool :=
  let t := Certificates.MaxD2Perm.wT Certificates.HSU35.dataU (hsU35GenWords.getD k [])
  allBelow 50 fun i =>
    t[hsU35Labels[i]!]! == hsU35Labels[(HNUnitaryBridge.smallPerms[k]!)[i]!]!

@[expose] def hsU35Check (_ : Unit := ()) : Bool := labelsOK () && allBelow 6 actsOK

end Certificates.ThreeFourTwoHSU35
