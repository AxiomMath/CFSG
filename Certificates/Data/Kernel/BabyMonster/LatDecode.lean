module

public import Certificates.Data.CFSGNative.MonsterB.DyadicData
import Init.Internal.Order.While

public section

namespace CFSG.KC.BM.Lat

open CFSG.Monster.B.Dyadic.Native

@[expose] def lineBreakOf (t : String) : Nat := Id.run do
  let b := t.toUTF8
  let mut k := 0
  while k < b.size && b.get! k != 10 do
    k := k + 1
  return k

@[expose] def diagExpOf (t : String) : Array Nat :=
  let b := t.toUTF8
  Array.ofFn (n := dim) fun i => (b.get! i.val).toNat - 48

@[expose] def upperBitsOf (t : String) : ByteArray :=
  let b := t.toUTF8
  let stop := Id.run do
    let mut k := lineBreakOf t + 1
    while k < b.size && b.get! k != 10 do
      k := k + 1
    return k
  b64decode b (lineBreakOf t + 1) stop

@[expose] def basisRowsOf (t : String) : Array ByteArray := Id.run do
  let n := dim
  let bits := upperBitsOf t
  let mut rows : Array ByteArray := Array.mkEmpty n
  let mut acc : Nat := 0
  let mut nb : Nat := 0
  let mut pos : Nat := 0
  for i in [0:n] do
    let mut row := ByteArray.mk (Array.replicate n 0)
    row := row.set! i (UInt8.ofNat (1 <<< (diagExpOf t)[i]!))
    for j in [i + 1:n] do
      while nb < 7 do
        acc := acc ||| ((bits.get! pos).toNat <<< nb)
        pos := pos + 1
        nb := nb + 8
      row := row.set! j (UInt8.ofNat (acc &&& 127))
      acc := acc >>> 7
      nb := nb - 7
    rows := rows.push row
  return rows

@[expose] def expCountOf (e : Array Nat) (k : Nat) : Nat :=
  ((List.range dim).map fun i => if e[i]! = k then 1 else 0).sum

@[expose] def expDefectOf (e : Array Nat) : Nat := ((List.range dim).map fun i => 7 - e[i]!).sum

end CFSG.KC.BM.Lat

end
