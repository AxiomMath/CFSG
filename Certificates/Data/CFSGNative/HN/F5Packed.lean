module

public import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.F5.Native

structure W17 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  w8 : UInt64
  w9 : UInt64
  w10 : UInt64
  w11 : UInt64
  w12 : UInt64
  w13 : UInt64
  w14 : UInt64
  w15 : UInt64
  w16 : UInt64
deriving Inhabited

namespace W17

@[inline, expose] def word (a : W17) : Nat → UInt64
  | 0 => a.w0
  | 1 => a.w1
  | 2 => a.w2
  | 3 => a.w3
  | 4 => a.w4
  | 5 => a.w5
  | 6 => a.w6
  | 7 => a.w7
  | 8 => a.w8
  | 9 => a.w9
  | 10 => a.w10
  | 11 => a.w11
  | 12 => a.w12
  | 13 => a.w13
  | 14 => a.w14
  | 15 => a.w15
  | 16 => a.w16
  | _ => 0

@[inline, expose] def add (a b : W17) : W17 :=
  ⟨a.w0 + b.w0, a.w1 + b.w1, a.w2 + b.w2, a.w3 + b.w3, a.w4 + b.w4, a.w5 + b.w5, a.w6 + b.w6,
    a.w7 + b.w7, a.w8 + b.w8, a.w9 + b.w9, a.w10 + b.w10, a.w11 + b.w11, a.w12 + b.w12,
    a.w13 + b.w13, a.w14 + b.w14, a.w15 + b.w15, a.w16 + b.w16⟩

@[expose] def zero : W17 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[inline, expose] def lane (a : W17) (i : Nat) : Nat :=
  ((a.word (i / 8) >>> (UInt64.ofNat (8 * (i % 8)))) &&& 0xFF).toNat

end W17

@[inline, expose] def packWord (f : Nat → Nat) : UInt64 :=
  UInt64.ofNat (f 0 + 256 * (f 1 + 256 * (f 2 + 256 * (f 3 + 256 * (f 4 + 256 * (f 5 +
    256 * (f 6 + 256 * f 7)))))))

@[expose] def packW (f : Nat → Nat) : W17 :=
  ⟨packWord (fun l => f l), packWord (fun l => f (8 + l)), packWord (fun l => f (16 + l)),
    packWord (fun l => f (24 + l)), packWord (fun l => f (32 + l)), packWord (fun l => f (40 + l)),
    packWord (fun l => f (48 + l)), packWord (fun l => f (56 + l)), packWord (fun l => f (64 + l)),
    packWord (fun l => f (72 + l)), packWord (fun l => f (80 + l)), packWord (fun l => f (88 + l)),
    packWord (fun l => f (96 + l)), packWord (fun l => f (104 + l)),
    packWord (fun l => f (112 + l)), packWord (fun l => f (120 + l)),
    packWord (fun l => f (128 + l))⟩

@[inline, expose] def ent (d : Nat) (M : Array (Array Nat)) (i j : Nat) : Nat :=
  if j < d then M[i]![j]! else 0

@[inline, expose] def frSum (d : Nat) (M : Array (Array Nat)) (i g c : Nat) : Nat :=
  c % 5 * ent d M i (3 * g) + c / 5 % 5 * ent d M i (3 * g + 1) +
    c / 25 % 5 * ent d M i (3 * g + 2)

@[expose] def frEntry (r d : Nat) (M : Array (Array Nat)) (g c : Nat) : W17 :=
  packW fun i => if i < r then frSum d M i g c % 5 else 0

@[inline, expose] def ngroups (d : Nat) : Nat := (d + 2) / 3

@[expose] def frTable (r d : Nat) (M : Array (Array Nat)) : Array W17 :=
  Array.ofFn (n := ngroups d * 125) fun t => frEntry r d M (t.val / 125) (t.val % 125)

@[inline, expose] def dig (v : ByteArray) (j : Nat) : Nat :=
  if j < v.size then (v.get! j).toNat else 0

@[inline, expose] def grpIdx (v : ByteArray) (g : Nat) : Nat :=
  dig v (3 * g) + 5 * dig v (3 * g + 1) + 25 * dig v (3 * g + 2)

@[expose] def frAcc (d : Nat) (T : Array W17) (v : ByteArray) : W17 :=
  Nat.fold (ngroups d) (fun g _ acc => acc.add T[125 * g + grpIdx v g]!) W17.zero

@[expose] def unpackW (r : Nat) (a : W17) : ByteArray :=
  ⟨Array.ofFn (n := r) fun i => UInt8.ofNat (a.lane i.val % 5)⟩

@[expose] def mulW (r d : Nat) (T : Array W17) (v : ByteArray) : ByteArray :=
  unpackW r (frAcc d T v)

@[expose] def canonB (d : Nat) (v : ByteArray) : Bool :=
  v.size == d && CFSG.Sporadic.Th.Native.allIn 0 d fun j => (v.get! j).toNat < 5

@[expose] def bytesOfDigits (s : String) : ByteArray :=
  ⟨(s.toList.map fun c =>
    UInt8.ofNat (if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0)).toArray⟩

@[expose] def bytesToNats (v : ByteArray) : Array Nat := v.data.map fun b => b.toNat

end CFSG.Sporadic.F5.Native
