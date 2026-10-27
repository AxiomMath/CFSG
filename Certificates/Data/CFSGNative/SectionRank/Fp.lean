module

public import Certificates.Data.CFSGNative.SectionRank.Elem3
public import Certificates.Data.CFSGNative.He.Fp

public section

namespace CFSG.SectionRank.Native

open CFSG.Sporadic.He.Native

@[expose] def vecMulRow (p d : Nat) (v : Array Nat) (X : Array (Array Nat)) : Array Nat :=
  Array.ofFn (n := d) fun k => dot p d v (col d X k.val)

@[expose] def opsP (p d : Nat) : Ops (Array (Array Nat)) (Array Nat) where
  decode := rowsOf p d
  mul := mulM p d
  one := idM d
  eq X Y := X == Y
  vmul := vecMulRow p d
  unit k := Array.ofFn (n := d) fun j => if j.val = k then 1 else 0
  vne u w := (List.range d).any fun j => u[j]! % p != w[j]! % p

end CFSG.SectionRank.Native
