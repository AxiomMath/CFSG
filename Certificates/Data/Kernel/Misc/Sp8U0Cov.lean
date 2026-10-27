module

public import Certificates.Data.Kernel.Misc.Sp8U0

public section

namespace CFSG.KD.Sp8U0

open CFSG.KD.BfsK CFSG.KD.Sp8Syl3 CFSG.KC.Mat8P CFSG.KC.Loop

@[expose] noncomputable def cst (Q : Nat → Nat) (x s : Nat) : Nat :=
  mulP (mulP (Q (Nat.mul 2 s)) x) (Q (Nat.add (Nat.mul 2 s) 1))

@[expose] noncomputable def oK (Q : Nat → Nat) (k : Nat) : Nat := Q (Nat.add 10 k)

@[expose] noncomputable def nK (Q : Nat → Nat) (k : Nat) : Nat := Q (Nat.add 143 k)

@[expose] noncomputable def orbAt (Q : Nat → Nat) (k o n : Nat) : Bool :=
  Nat.blt 0 n && Nat.ble n 128 && tableKk Q (cst Q) o n 5 2 10 2

@[expose] noncomputable def orbK (Q : Nat → Nat) : Bool :=
  allBelow 133 3 fun k => orbAt Q k (oK Q k) (nK Q k)

@[expose] noncomputable def covAt (Q : Nat → Nat) (X w : Nat) : Bool :=
  !(Nat.beq (mulP X X) oneP) || Nat.beq X oneP ||
    (Nat.blt (Nat.shiftRight w 8) 133 && Nat.blt (Nat.land w 255) (nK Q (Nat.shiftRight w 8)) &&
      Nat.beq (recX Q (oK Q (Nat.shiftRight w 8)) (Nat.land w 255)) X)

@[expose] noncomputable def covK (R Q : Nat → Nat) : Bool :=
  allBelow 65536 1024 fun t => covAt Q (recX R 9 t) (Q (Nat.add 4248 t))

end CFSG.KD.Sp8U0

end
