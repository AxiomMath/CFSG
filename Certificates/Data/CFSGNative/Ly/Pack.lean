module

public section

namespace CFSG.Sporadic.Ly.Native

structure W14 where
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
deriving Inhabited

namespace W14

@[inline, expose] def word (a : W14) : Nat → UInt64
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
  | _ => 0

@[inline, expose] def add (a b : W14) : W14 :=
  ⟨a.w0 + b.w0, a.w1 + b.w1, a.w2 + b.w2, a.w3 + b.w3, a.w4 + b.w4, a.w5 + b.w5, a.w6 + b.w6,
    a.w7 + b.w7, a.w8 + b.w8, a.w9 + b.w9, a.w10 + b.w10, a.w11 + b.w11, a.w12 + b.w12,
    a.w13 + b.w13⟩

@[inline, expose] def smul (c : UInt64) (a : W14) : W14 :=
  ⟨c * a.w0, c * a.w1, c * a.w2, c * a.w3, c * a.w4, c * a.w5, c * a.w6, c * a.w7, c * a.w8,
    c * a.w9, c * a.w10, c * a.w11, c * a.w12, c * a.w13⟩

@[expose] def zero : W14 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[inline, expose] def lane (a : W14) (i : Nat) : Nat :=
  ((a.word (i / 8) >>> (UInt64.ofNat (8 * (i % 8)))) &&& 0xFF).toNat

end W14

@[inline, expose] def packWord (f : Nat → Nat) : UInt64 :=
  UInt64.ofNat (f 0 + 256 * (f 1 + 256 * (f 2 + 256 * (f 3 + 256 * (f 4 + 256 * (f 5 +
    256 * (f 6 + 256 * f 7)))))))

@[expose] def packW (f : Nat → Nat) : W14 :=
  ⟨packWord (fun l => f l), packWord (fun l => f (8 + l)), packWord (fun l => f (16 + l)),
    packWord (fun l => f (24 + l)), packWord (fun l => f (32 + l)), packWord (fun l => f (40 + l)),
    packWord (fun l => f (48 + l)), packWord (fun l => f (56 + l)), packWord (fun l => f (64 + l)),
    packWord (fun l => f (72 + l)), packWord (fun l => f (80 + l)), packWord (fun l => f (88 + l)),
    packWord (fun l => f (96 + l)), packWord (fun l => f (104 + l))⟩

@[inline, expose] def byteOf (w : UInt64) (l : Nat) : Nat :=
  ((w >>> (UInt64.ofNat (8 * l))) &&& 0xFF).toNat

@[inline, expose] def redWord (w : UInt64) : UInt64 :=
  packWord fun l => byteOf w l % 5

@[inline, expose] def W14.red (a : W14) : W14 :=
  ⟨redWord a.w0, redWord a.w1, redWord a.w2, redWord a.w3, redWord a.w4, redWord a.w5,
    redWord a.w6, redWord a.w7, redWord a.w8, redWord a.w9, redWord a.w10, redWord a.w11,
    redWord a.w12, redWord a.w13⟩

@[inline, expose] def pushRed (b : ByteArray) (w : UInt64) : ByteArray :=
  ((((((((b.push (UInt8.ofNat (byteOf w 0 % 5))).push (UInt8.ofNat (byteOf w 1 % 5))).push
    (UInt8.ofNat (byteOf w 2 % 5))).push (UInt8.ofNat (byteOf w 3 % 5))).push
    (UInt8.ofNat (byteOf w 4 % 5))).push (UInt8.ofNat (byteOf w 5 % 5))).push
    (UInt8.ofNat (byteOf w 6 % 5))).push (UInt8.ofNat (byteOf w 7 % 5)))

@[expose] def W14.digits (a : W14) : ByteArray :=
  Nat.fold 14 (fun q _ b => pushRed b (a.word q)) (ByteArray.emptyWithCapacity 112)

@[inline, expose] def ent (M : Array (Array Nat)) (i j : Nat) : Nat :=
  if i < 111 ∧ j < 111 then M[i]![j]! else 0

@[inline, expose] def frSum (M : Array (Array Nat)) (i g c : Nat) : Nat :=
  c % 5 * ent M i (3 * g) + c / 5 % 5 * ent M i (3 * g + 1) + c / 25 % 5 * ent M i (3 * g + 2)

@[expose] def frEntry (M : Array (Array Nat)) (g c : Nat) : W14 :=
  packW fun i => frSum M i g c % 5

@[expose] def frTable (M : Array (Array Nat)) : Array W14 :=
  Array.ofFn (n := 37 * 125) fun t => frEntry M (t.val / 125) (t.val % 125)

@[expose] def rowProd (T : Array W14) (key : ByteArray) (r : Nat) : W14 :=
  Nat.fold 37 (fun g _ acc => acc.add T[125 * g + (key.get! (37 * r + g)).toNat]!) W14.zero

@[inline, expose] def keyDigit (key : ByteArray) (p : Nat) : Nat :=
  (key.get! (p / 3)).toNat / (5 ^ (p % 3)) % 5

@[inline, expose] def code3 (a b c : Nat) : UInt8 :=
  UInt8.ofNat (a % 5 + 5 * (b % 5) + 25 * (c % 5))

end CFSG.Sporadic.Ly.Native
