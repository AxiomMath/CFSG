module

public import Certificates.Data.Kernel.Misc.BfsK
public import Certificates.Data.Kernel.Mat8P

public section

namespace CFSG.KD.Sp8Syl3

open CFSG.KD.BfsK CFSG.KC.Mat8P CFSG.KC.Loop

@[expose] noncomputable def rst (R : Nat → Nat) (x s : Nat) : Nat := mulP x (R s)

@[expose] noncomputable def tabEK (R : Nat → Nat) (n : Nat) : Bool :=
  Nat.beq (recX R 11 0) oneP && tableKk R (rst R) 11 n 4 2 6 2

@[expose] noncomputable def tabPK (R : Nat → Nat) (n : Nat) : Bool :=
  Nat.beq (recX R 93 0) oneP && tableKk R (rst R) 93 n 5 4 19 4

@[expose] noncomputable def commN (x y : Nat) : Bool := Nat.beq (mulP x y) (mulP y x)

@[expose] noncomputable def e0K (R : Nat → Nat) : Bool :=
  allBelow 81 2 fun t =>
    commN (recX R 11 t) (R 0) && commN (recX R 11 t) (R 1) && commN (recX R 11 t) (R 2) &&
      commN (recX R 11 t) (R 3) &&
      Nat.beq (mulP (recX R 11 t) (mulP (recX R 11 t) (recX R 11 t))) oneP

@[expose] noncomputable def inE (R : Nat → Nat) (w p : Nat) : Bool :=
  Nat.blt w 81 && Nat.beq (recX R 11 w) p

@[expose] noncomputable def cntP (R : Nat → Nat) (p : Nat) : Nat :=
  ((List.range 243).filter fun s => commN p (recX R 93 s)).length

@[expose] noncomputable def cpK (R : Nat → Nat) (m : Nat) : Bool :=
  allBelow 243 4 fun t => inE R (recF R 93 14 t) (recX R 93 t) || Nat.blt (cntP R (recX R 93 t)) m

@[expose] noncomputable def conjAt (R : Nat → Nat) (c e p : Nat) : Bool :=
  Nat.blt c 3 && Nat.beq (recX R 11 e) (mulP (mulP (R (Nat.add 5 c)) p) (R (Nat.add 8 c))) &&
    Nat.beq (mulP (R (Nat.add 5 c)) p) (mulP (recX R 11 e) (R (Nat.add 5 c)))

@[expose] noncomputable def conjK (R : Nat → Nat) : Bool :=
  allBelow 243 4 fun t =>
    !(Nat.beq (mulP (recX R 93 t) (mulP (recX R 93 t) (recX R 93 t))) oneP) ||
      Nat.beq (recX R 93 t) oneP || inE R (recF R 93 14 t) (recX R 93 t) ||
      (Nat.ble 81 (recF R 93 14 t) &&
        conjAt R (Nat.div (Nat.sub (recF R 93 14 t) 81) 81) (Nat.mod (Nat.sub (recF R 93 14 t) 81) 81)
          (recX R 93 t))

end CFSG.KD.Sp8Syl3

end
