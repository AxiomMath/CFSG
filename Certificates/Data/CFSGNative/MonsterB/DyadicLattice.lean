module

public import Certificates.Data.CFSGNative.MonsterB.DyadicData
public import Certificates.Data.CFSGNative.MonsterB.DyadicElim

public section

namespace CFSG.Monster.B.Dyadic.Native

@[expose] def containStart (rows : Array ByteArray) (pexp : Array Nat) (i : Nat) : ByteArray :=
  let s : UInt8 := UInt8.ofNat (1 <<< (7 - pexp[i]!))
  let rowI := rows[i]!
  ByteArray.mk (Array.ofFn (n := dim) fun l =>
    if i < l.val then (s * rowI.get! l.val) &&& 127 else 0)

@[expose] def containRow (rows : Array ByteArray) (pexp : Array Nat) (i : Nat) : Bool :=
  allZero dim (elimGo 127 rows pexp dim (i + 1) (containStart rows pexp i) (zeroBytes dim)).1

@[expose] def containOK (chunks : Nat) : Bool :=
  let rows := basisRows
  let pexp := diagExp
  rows.size == dim && pexp.size == dim &&
    allLt dim (fun i => rows[i]!.size == dim && decide (pexp[i]! ≤ 7) &&
      (rows[i]!.get! i).toNat == 1 <<< pexp[i]! &&
      allLt dim (fun k => if k < i then rows[i]!.get! k == 0
        else decide (k = i) || decide ((rows[i]!.get! k).toNat < 128))) &&
    parLt dim chunks (containRow rows pexp)

end CFSG.Monster.B.Dyadic.Native
