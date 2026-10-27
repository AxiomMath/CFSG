module

public import Certificates.Data.CFSGNative.MonsterB.DyadicLattice
public import Certificates.Data.CFSGNative.MonsterB.PacketData

public section

namespace CFSG.Monster.B.Dyadic.Native

@[expose] def selIdx (g : Nat) : Nat := if g = 0 then 1 else g + 22

@[inline, expose] def toU32 (m : Int) : UInt32 := UInt32.ofNat (m % 4294967296).toNat

@[expose] def genRows (g : Nat) : Array (Array (Nat × UInt32)) :=
  (CFSG.Monster.B.Native.packetRows[selIdx g]!).map fun row => row.map fun e => (e.1, toU32 e.2)

@[expose] def addRow (acc : Array UInt32) (b : UInt32) : List (Nat × UInt32) → Array UInt32
  | [] => acc
  | (u, m) :: rest => addRow (acc.modify u (· + b * m)) b rest

@[expose] def mulGo (M : Array (Array (Nat × UInt32))) (rowI : ByteArray) (n : Nat) :
    Nat → Array UInt32 → Array UInt32
  | t, acc =>
    if t < n then
      let b := rowI.get! t
      mulGo M rowI n (t + 1) (if b == 0 then acc else addRow acc b.toUInt32 (M[t]!).toList)
    else acc
termination_by t => n - t

@[expose] def wRow (sh : Nat) (rows : Array ByteArray) (M : Array (Array (Nat × UInt32)))
    (i : Nat) : Option ByteArray :=
  let n := dim
  let m := 2 ^ sh
  let acc := mulGo M rows[i]! n 0 (Array.replicate n 0)
  if allLt n (fun u => acc[u]!.toNat % m == 0) then
    some (ByteArray.mk (Array.ofFn (n := n) fun u =>
      UInt8.ofNat ((acc[u.val]!.toNat >>> sh) % 256)))
  else none

@[expose] def reduceRow (sh : Nat) (rows : Array ByteArray) (pexp : Array Nat)
    (M : Array (Array (Nat × UInt32))) (i : Nat) : Option ByteArray :=
  match wRow sh rows M i with
  | none => none
  | some w =>
    let r := elimGo 255 rows pexp dim 0 w (zeroBytes dim)
    if allZero dim r.1 then some r.2 else none

@[expose] def reduceOK (g chunks : Nat) : Bool :=
  let rows := basisRows
  let pexp := diagExp
  let M := genRows g
  M.size == dim && parLt dim chunks fun i => (reduceRow 3 rows pexp M i).isSome

@[expose] def reduceAllOK (chunks : Nat) : Bool := allLt 26 fun g => reduceOK g chunks

@[expose] def packBits : List Bool → Nat
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * packBits l

@[expose] def packByte (bit : Nat → Bool) : UInt8 := UInt8.ofNat (packBits ((List.range 8).map bit))

@[expose] def binRow (sh : Nat) (rows : Array ByteArray) (pexp : Array Nat)
    (M : Array (Array (Nat × UInt32))) (i : Nat) : ByteArray :=
  match reduceRow sh rows pexp M i with
  | none => zeroBytes 552
  | some qs => ByteArray.mk (Array.ofFn (n := 552) fun b => packByte fun u =>
      decide (8 * b.val + u < dim) && (qs.get! (8 * b.val + u) &&& 1 == 1))

@[noinline, expose] def binParts (g chunks sz : Nat) : Array (Task (Array ByteArray)) :=
  let rows := basisRows
  let pexp := diagExp
  let M := genRows g
  Array.ofFn (n := chunks) fun c => Task.spawn fun _ => Array.ofFn (n := sz) fun j =>
    if c.val * sz + j.val < dim then binRow 3 rows pexp M (c.val * sz + j.val) else zeroBytes 552

@[noinline, expose] def assembleRows (parts : Array (Task (Array ByteArray))) (sz : Nat) :
    Array ByteArray :=
  Array.ofFn (n := dim) fun k => (parts[k.val / sz]!).get[k.val % sz]!

@[expose] def binRows (g chunks : Nat) : Array ByteArray :=
  assembleRows (binParts g chunks (dim / chunks + 1)) (dim / chunks + 1)

end CFSG.Monster.B.Dyadic.Native
