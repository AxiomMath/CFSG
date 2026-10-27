module

public section

namespace CFSG.Monster.B.Binary.Native

@[expose] def shaK (_ : Unit := ()) : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[expose] def shaH0 (_ : Unit := ()) : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline, expose] def rotr (x : UInt32) (k : UInt32) : UInt32 := (x >>> k) ||| (x <<< (32 - k))

@[inline, expose] def word (byte : Nat → UInt8) (o t : Nat) : UInt32 :=
  ((byte (o + 4 * t)).toUInt32 <<< 24) ||| ((byte (o + 4 * t + 1)).toUInt32 <<< 16) |||
    ((byte (o + 4 * t + 2)).toUInt32 <<< 8) ||| (byte (o + 4 * t + 3)).toUInt32

@[expose] def compress (byte : Nat → UInt8) (h : Array UInt32) (o : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for t in [0:16] do
    w := w.push (word byte o t)
  for t in [16:64] do
    let x := w[t - 15]!
    let y := w[t - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for t in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := hh + S1 + ch + shaK[t]! + w[t]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
    h[7]! + hh]

@[expose] def u32le (x : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat x, UInt8.ofNat (x >>> 8), UInt8.ofNat (x >>> 16), UInt8.ofNat (x >>> 24)]⟩

@[expose] def sha256Nat (m : ByteArray) : Nat := Id.run do
  let len := m.size
  let total := (len + 9 + 63) / 64 * 64
  let bitLen := 8 * len
  let byte : Nat → UInt8 := fun i =>
    if i < len then m.get! i
    else if i = len then 0x80
    else if i + 8 < total then 0
    else UInt8.ofNat (bitLen >>> (8 * (total - 1 - i)))
  let mut h := shaH0
  let mut o := 0
  while o < total do
    h := compress byte h o
    o := o + 64
  let mut r : Nat := 0
  for t in [0:8] do
    r := (r <<< 32) ||| h[t]!.toNat
  return r

end CFSG.Monster.B.Binary.Native
