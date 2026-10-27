module

public import Certificates.Data.Kernel.F2Word
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.CFSGNative.Co2Smith.Pin

public section

namespace CFSG.KC.Co2SmithS

open CFSG.KC.F2W CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def xr (c i : Nat) : Nat :=
  (c >>> (i / 2) &&& 1) <<< (i % 2) ||| (c >>> (4 + i / 2) &&& 1) <<< (2 + i % 2) |||
    (c >>> (8 + i / 2) &&& 1) <<< (4 + i % 2) ||| (c >>> (12 + i / 2) &&& 1) <<< (6 + i % 2)

@[expose] noncomputable def xK (c : Nat) : Nat := orN 8 fun i => Nat.shiftLeft (xr c i) (Nat.mul 8 i)

@[expose] noncomputable def pow8 (M e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (idF 8) (fun _ acc => mulW 8 acc M) e

@[expose] noncomputable def fixK8 (X : Nat) : Bool :=
  (List.range 8).all fun a => vmF 8 (trK 8 X) (1 <<< a) == 1 <<< a

@[expose] noncomputable def wK8 (S : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (idF 8) (fun k _ acc => mulW 8 (S k) acc) w

@[expose] noncomputable def pinK (S : Nat → Nat) (c : Nat) : Bool :=
  pinRels.all fun r => fixK8 (pow8 (mulW 8 (xK c) (wK8 S r.1)) r.2)

end CFSG.KC.Co2SmithS

end
