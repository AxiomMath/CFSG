module

public import Certificates.Data.Kernel.Misc.G22W

public section

namespace CFSG.KD.Sp6W

open CFSG.KC.Mat8P CFSG.KD.G22W CFSG.KC.Loop CFSG.KD.BfsK

@[expose] def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] def bfR (x y : Nat) : Bool :=
  (x.testBit 0 && y.testBit 3) ^^ (x.testBit 3 && y.testBit 0) ^^
  (x.testBit 1 && y.testBit 4) ^^ (x.testBit 4 && y.testBit 1) ^^
  (x.testBit 2 && y.testBit 5) ^^ (x.testBit 5 && y.testBit 2)

@[expose] def isoC (c0 c1 c2 c3 c4 c5 : Nat) : Bool :=
  (c1 != 0 && !bfR c0 c1) &&
  (c2 != 0 && !bfR c0 c2 && !bfR c1 c2) &&
  (c3 != 0 && bfR c0 c3 && !bfR c1 c3 && !bfR c2 c3) &&
  (c4 != 0 && !bfR c0 c4 && bfR c1 c4 && !bfR c2 c4 && !bfR c3 c4) &&
  (c5 != 0 && !bfR c0 c5 && !bfR c1 c5 && bfR c2 c5 && !bfR c3 c5 && !bfR c4 c5)

@[expose] def isoK (x : Nat) : Bool :=
  isoC (Nat.land x 255) (Nat.land (Nat.shiftRight x 8) 255) (Nat.land (Nat.shiftRight x 16) 255)
    (Nat.land (Nat.shiftRight x 24) 255) (Nat.land (Nat.shiftRight x 32) 255)
    (Nat.land (Nat.shiftRight x 40) 255)

@[expose] def fiveY (y : Nat) : Bool :=
  !(Nat.beq y oneP) && Nat.beq (mulP y (mulP (mulP y y) (mulP y y))) oneP

@[expose] def fiveP (x : Nat) : Bool :=
  fiveY (mulP (mulP (mulP x x) x) (mulP (mulP x x) x))

@[expose] def uL : List Nat :=
  [3, 7, 8, 9, 13, 18, 19, 21, 25, 30, 31, 37, 40, 42, 45, 49, 51, 52, 53, 55, 58]

@[expose] def keyC (c0 c1 c2 c3 c4 c5 : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ c1 ^^^ 0 ^^^ 0 ^^^ 0 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ c1 ^^^ c2 ^^^ 0 ^^^ 0 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (0 ^^^ 0 ^^^ 0 ^^^ c3 ^^^ 0 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ 0 ^^^ 0 ^^^ c3 ^^^ 0 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ 0 ^^^ c2 ^^^ c3 ^^^ 0 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (0 ^^^ c1 ^^^ 0 ^^^ 0 ^^^ c4 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ c1 ^^^ 0 ^^^ 0 ^^^ c4 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ 0 ^^^ c2 ^^^ 0 ^^^ c4 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ 0 ^^^ 0 ^^^ c3 ^^^ c4 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ 0)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ 0 ^^^ c2 ^^^ 0 ^^^ 0 ^^^ c5)) <|
  Nat.lor (Nat.shiftLeft 1 (0 ^^^ 0 ^^^ 0 ^^^ c3 ^^^ 0 ^^^ c5)) <|
  Nat.lor (Nat.shiftLeft 1 (0 ^^^ c1 ^^^ 0 ^^^ c3 ^^^ 0 ^^^ c5)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ 0 ^^^ c2 ^^^ c3 ^^^ 0 ^^^ c5)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ 0 ^^^ 0 ^^^ 0 ^^^ c4 ^^^ c5)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ c1 ^^^ 0 ^^^ 0 ^^^ c4 ^^^ c5)) <|
  Nat.lor (Nat.shiftLeft 1 (0 ^^^ 0 ^^^ c2 ^^^ 0 ^^^ c4 ^^^ c5)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ 0 ^^^ c2 ^^^ 0 ^^^ c4 ^^^ c5)) <|
  Nat.lor (Nat.shiftLeft 1 (c0 ^^^ c1 ^^^ c2 ^^^ 0 ^^^ c4 ^^^ c5)) <|
  Nat.lor (Nat.shiftLeft 1 (0 ^^^ c1 ^^^ 0 ^^^ c3 ^^^ c4 ^^^ c5)) 0

@[expose] def keyK (x : Nat) : Nat :=
  keyC (Nat.land x 255) (Nat.land (Nat.shiftRight x 8) 255) (Nat.land (Nat.shiftRight x 16) 255)
    (Nat.land (Nat.shiftRight x 24) 255) (Nat.land (Nat.shiftRight x 32) 255)
    (Nat.land (Nat.shiftRight x 40) 255)

@[expose] def T64 : Nat := 18446744073709551616

@[expose] noncomputable def zRec (Z : Nat → Nat) (j : Nat) : Bool :=
  Nat.blt (Z j) T64 && goodK (Z j) && isoK (Z j) && fiveP (Z j)

@[expose] noncomputable def kW (W : Nat → Nat) (t : Nat) : Nat := Nat.land (W t) M64

@[expose] noncomputable def jW (W : Nat → Nat) (t : Nat) : Nat :=
  Nat.land (Nat.shiftRight (W t) 64) 65535

@[expose] noncomputable def hW (W : Nat → Nat) (t : Nat) : Nat := Nat.shiftRight (W t) 80

@[expose] noncomputable def wRec (N Z W : Nat → Nat) (m nz t : Nat) : Bool :=
  letB (W t) fun r => letB (kW W t) fun k => letB (jW W t) fun j => letB (hW W t) fun h =>
    Nat.blt j nz && Nat.blt h 42 &&
      letB (mulP (N h) (Z j)) (fun y => Nat.beq (keyK y) k) &&
      bIf(Nat.blt (Nat.add t 1) m, Nat.blt k (kW W (Nat.add t 1)), Nat.blt 0 (Nat.add r 1))

@[expose] noncomputable def zRange (Z : Nat → Nat) (nz hi : Nat) : Bool := allBelow nz hi (zRec Z)

@[expose] noncomputable def wRange (N Z W : Nat → Nat) (m nz lo n hi : Nat) : Bool :=
  allBelow n hi fun i => wRec N Z W m nz (Nat.add lo i)

end CFSG.KD.Sp6W

end
