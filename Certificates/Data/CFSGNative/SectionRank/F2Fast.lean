module

public import Certificates.Data.CFSGNative.SectionRank.Elem3
public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.SectionRank.Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def frEntry (Y : Array Nat) (k c : Nat) : Nat :=
  (List.range 8).foldl
    (fun acc i => if c.testBit i then acc ^^^ (Y[8 * k + i]?.getD 0) else acc) 0

@[expose] def frTable (nb : Nat) (Y : Array Nat) : Array Nat :=
  Array.ofFn (n := nb * 256) fun t => frEntry Y (t.val / 256) (t.val % 256)

@[expose] def frApply (nw : Nat) (T : Array Nat) (x : Nat) : Nat :=
  (List.range nw).foldl (fun acc l =>
    let w := (x >>> (32 * l)) % 4294967296
    (List.range 4).foldl
      (fun acc b => acc ^^^ (T[256 * (4 * l + b) + (w >>> (8 * b)) % 256]?.getD 0)) acc) 0

@[expose] def frMul (d : Nat) (X Y : Array Nat) : Array Nat :=
  let nw := (d + 31) / 32
  let T := frTable (4 * nw) Y
  X.map (frApply nw T)

@[expose] def ops2fr (d : Nat) : Ops (Array Nat) Nat where
  decode := rowsOfPayload d
  mul := frMul d
  one := idRows d
  eq X Y := X == Y
  vmul v X := vecMulN d X v
  unit k := 1 <<< k
  vne u w := (List.range d).any fun j => u.testBit j != w.testBit j

end CFSG.SectionRank.Native
