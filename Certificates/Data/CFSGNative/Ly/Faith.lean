module

public import Certificates.Data.CFSGNative.Ly.Pack
public import Certificates.Data.CFSGNative.He.Fp

public section

namespace CFSG.Sporadic.Ly.Native

open CFSG.Sporadic.He.Native

@[expose] def digitsOf (s : String) : Array Nat := s.toList.toArray.map fun c => c.toNat - '0'.toNat

@[expose] def matOfDigits (s : String) : Array (Array Nat) :=
  let e := digitsOf s
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j => e[111 * i.val + j.val]!

@[expose] def transM (X : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j => X[j.val]![i.val]!

@[expose] def keyTensor (key : ByteArray) : Array (Array Nat) :=
  let U := Array.ofFn (n := 111) fun j => Array.ofFn (n := 7) fun a =>
    keyDigit key (111 * a.val + j.val)
  let C := Array.ofFn (n := 7) fun a => Array.ofFn (n := 7) fun b =>
    keyDigit key (777 + 7 * a.val + b.val)
  let UC := Array.ofFn (n := 111) fun j => Array.ofFn (n := 7) fun b =>
    (Nat.fold 7 (fun a _ acc => acc + U[j.val]![a]! * C[a]![b.val]!) 0) % 5
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j =>
    (Nat.fold 7 (fun b _ acc => acc + UC[i.val]![b]! * U[j.val]![b]!) 0) % 5

@[expose] def cyclicVecs (Z : Array (Array (Array Nat))) (v : Array Nat) (par op : Array Nat) :
    Array (Array Nat) :=
  Nat.fold 110 (fun t _ cs => cs.push (mulVec 5 111 Z[op[t]!]! cs[par[t]!]!)) #[v]

@[expose] def faithZ (qkeys : Array ByteArray) (F : Array (Array Nat)) :
    Array (Array (Array Nat)) :=
  qkeys.map fun k => mulM 5 111 (keyTensor k) F

@[expose] def faithN (Z : Array (Array (Array Nat))) (ab : Nat × Nat) (mu : Nat) :
    Array (Array Nat) :=
  let z := mulM 5 111 Z[ab.1]! Z[ab.2]!
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j =>
    (z[i.val]![j.val]! + (if i.val = j.val then 5 - mu % 5 else 0)) % 5

@[expose] def faithP (v w : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j =>
    ((if i.val = j.val then 1 else 0) + 4 * (v[i.val]! * w[j.val]!)) % 5

@[expose] def faithChecks (qkeys : Array ByteArray) (F Y Cinv : Array (Array Nat))
    (v w par op : Array Nat) (ab : Nat × Nat) (mu : Nat) : Bool :=
  let Z := faithZ qkeys F
  let N := faithN Z ab mu
  qkeys.size == 16 && ab.1 < 16 && ab.2 < 16 && v.size == 111 && w.size == 111 &&
    par.size == 110 && op.size == 110 &&
    (List.range 110).all (fun t => par[t]! < t + 1 && op[t]! < 16) &&
    mulVec 5 111 N v == Array.replicate 111 0 &&
    mulM 5 111 Y N == faithP v w &&
    mulM 5 111 (colsMat 111 (cyclicVecs Z v par op)) Cinv == idM 111

end CFSG.Sporadic.Ly.Native
