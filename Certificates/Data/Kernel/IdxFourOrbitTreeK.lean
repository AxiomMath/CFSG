module

public import Certificates.Data.Kernel.IdxFourChainK

public section

namespace CFSG.KC.IF4O

open CFSG.KC.IF4C

@[expose] noncomputable def pc6K (x : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.land x 1) (Nat.land (Nat.shiftRight x 1) 1))
    (Nat.land (Nat.shiftRight x 2) 1)) (Nat.land (Nat.shiftRight x 3) 1))
    (Nat.land (Nat.shiftRight x 4) 1)) (Nat.land (Nat.shiftRight x 5) 1)

@[expose] noncomputable def wtK (n : Nat) : Nat := pc6K (Nat.land (Nat.lor n (Nat.shiftRight n 6)) 63)

@[expose] noncomputable def peK (n : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add (pc6K (Nat.land n 63)) (Nat.mul 2 (pc6K (Nat.shiftRight n 6)))) (wtK n)) 3

@[expose] noncomputable def o378K (n : Nat) : Bool :=
  Nat.beq (wtK n) 2 || (Nat.beq (wtK n) 6 && Nat.beq (peK n) 0)

@[expose] noncomputable def singK (n : Nat) : Bool :=
  Nat.beq (wtK n) 2 || Nat.beq (wtK n) 4 || Nat.beq (wtK n) 6

@[expose] noncomputable def f24 (D n : Nat) : Nat := Nat.land (Nat.shiftRight D (Nat.mul 24 n)) 16777215

@[expose] noncomputable def parT (D n : Nat) : Nat := Nat.land (f24 D n) 4095

@[expose] noncomputable def genT (D n : Nat) : Nat := Nat.land (Nat.shiftRight (f24 D n) 12) 3

@[expose] noncomputable def depT (D n : Nat) : Nat := Nat.shiftRight (f24 D n) 14

@[expose] noncomputable def nodeOK (G D n : Nat) : Bool :=
  !singK n || Nat.beq n 3 || Nat.beq n 15 ||
    (Nat.blt (genT D n) 3 && singK (parT D n) &&
      (bif o378K (parT D n) then o378K n else !o378K n) &&
      Nat.blt (depT D (parT D n)) (depT D n) &&
      Nat.beq (ap12 (look G (genT D n)) (parT D n)) n)

@[expose] noncomputable def treeOK (G D : Nat) : Bool := allBelow 4096 (nodeOK G D)

end CFSG.KC.IF4O

end
