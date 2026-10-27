module

public import Certificates.Data.CFSGNative.H13.J4Chain12

public section

namespace CFSG.Quasithin.H13.J4.Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def pr12Pow (x : Pr12) : Nat → Pr12
  | 0 => pr12One
  | e + 1 => pr12Mul (pr12Pow x e) x

@[expose] def rows12Ne (X Y : Array Nat) : Bool :=
  (List.range 12).any fun i => (List.range 12).any fun j =>
    (X.getD i 0).testBit j != (Y.getD i 0).testBit j

@[expose] def eqModZ (z : Pr12) (X Y : Array Nat) : Bool :=
  X == Y || X == mulRows 12 Y z.1 || X == mulRows 12 (mulRows 12 Y z.1) z.1

@[expose] def pr12BWord (gs : Array Pr12) (w : List (Nat × Bool)) : Pr12 :=
  w.foldl (fun acc l => pr12Mul acc
    (if l.2 then gs[l.1]?.getD pr12One else pr12Inv (gs[l.1]?.getD pr12One))) pr12One

end CFSG.Quasithin.H13.J4.Native
