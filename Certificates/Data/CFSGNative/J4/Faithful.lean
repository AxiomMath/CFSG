module

public import Certificates.Data.CFSGNative.J4.Tables

public section

namespace CFSG.Sporadic.J4.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def sigRows (fs : Array V2) : Array V2 :=
  Array.ofFn (n := 112) fun i => V2.ofFn fun t => decide (t < fs.size) && (fs[t]?.getD V2.zero).testBit i.val

@[expose] def sigTable (keys : ByteArray) (tS : Array V2) (basis : Array Nat) (bits : Nat) :
    ByteArray := Id.run do
  let mut d := zeros (2 ^ bits)
  for t in [0:basis.size] do
    d := d.set! (frApply tS (rdV2 keys basis[t]!)).lo.toNat (UInt8.ofNat (t + 1))
  return d

@[expose] def uniqueSigOK (keys : ByteArray) (n : Nat) (tS : Array V2) (basis : Array Nat)
    (bits : Nat) (d : ByteArray) (chunks : Nat) : Bool :=
  basis.size < 255 && d.size == 2 ^ bits &&
    (List.range basis.size).all (fun t =>
      let s := frApply tS (rdV2 keys basis[t]!)
      s.hi == 0 && s.lo.toNat < 2 ^ bits && (d.get! s.lo.toNat).toNat == t + 1) &&
    parAllS n chunks fun i =>
      let s := frApply tS (rdV2 keys i)
      let e := if s.hi == 0 && s.lo.toNat < 2 ^ bits then (d.get! s.lo.toNat).toNat else 0
      e == 0 || basis[e - 1]?.getD 0 == i

end CFSG.Sporadic.J4.Native
