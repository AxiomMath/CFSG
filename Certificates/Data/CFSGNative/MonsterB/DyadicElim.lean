module

public section

namespace CFSG.Monster.B.Dyadic.Native

@[inline, expose] def allLt (n : Nat) (p : Nat → Bool) : Bool := Nat.all n fun i _ => p i

@[expose] def parLt (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let sz := n / chunks + 1
  ((List.range chunks).map fun c => Task.spawn fun _ =>
    allLt sz fun k => !(decide (c * sz + k < n)) || p (c * sz + k)).all Task.get

@[expose] def subRow (mask q : UInt8) (row : ByteArray) (n : Nat) : Nat → ByteArray → ByteArray
  | k, v =>
    if k < n then subRow mask q row n (k + 1) (v.set! k ((v.get! k - q * row.get! k) &&& mask))
    else v
termination_by k => n - k

@[expose] def elimGo (mask : UInt8) (rows : Array ByteArray) (pexp : Array Nat) (n : Nat) :
    Nat → ByteArray → ByteArray → ByteArray × ByteArray
  | j, v, qs =>
    if j < n then
      let x := v.get! j
      if x == 0 then elimGo mask rows pexp n (j + 1) v qs
      else
        let q := UInt8.ofNat (x.toNat >>> pexp[j]!)
        elimGo mask rows pexp n (j + 1) (subRow mask q rows[j]! n j v) (qs.set! j q)
    else (v, qs)
termination_by j => n - j

@[expose] def zeroBytes (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

@[expose] def allZero (n : Nat) (v : ByteArray) : Bool := allLt n fun k => v.get! k == 0

end CFSG.Monster.B.Dyadic.Native
