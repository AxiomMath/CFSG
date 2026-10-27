module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2.Native

@[inline, expose] def bget (b : ByteArray) (x : Nat) : Nat :=
  (b.get! (2 * x)).toNat + 256 * (b.get! (2 * x + 1)).toNat

@[inline, expose] def bofFn (n : Nat) (f : Nat → Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ByteArray.emptyWithCapacity (2 * n)
  for x in [0:n] do
    let v := f x
    b := (b.push (UInt8.ofNat (v % 256))).push (UInt8.ofNat ((v / 256) % 256))
  return b

@[expose] def bcomp (n : Nat) (t u : ByteArray) : ByteArray :=
  bofFn n fun x => bget t (bget u x)

@[expose] def bid (n : Nat) : ByteArray := bofFn n fun x => x

@[expose] def bofArr (n : Nat) (a : Array Nat) : ByteArray := bofFn n fun x => a[x]!

@[expose] def binvCand (n : Nat) (t : ByteArray) : ByteArray := Id.run do
  let mut r : ByteArray := ByteArray.mk (Array.replicate (2 * n) 0)
  for x in [0:n] do
    let y := bget t x
    r := (r.set! (2 * y) (UInt8.ofNat (x % 256))).set! (2 * y + 1) (UInt8.ofNat ((x / 256) % 256))
  return r

@[expose] def bisInv (n : Nat) (t r : ByteArray) : Bool :=
  allLt n fun x => decide (bget t x < n) && bget r (bget t x) == x

@[expose] def bEq (n : Nat) (t u : ByteArray) : Bool := allLt n fun x => bget t x == bget u x

end CFSG.YGroups.DCE
