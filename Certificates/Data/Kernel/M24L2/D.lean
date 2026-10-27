module

public import Certificates.Data.Kernel.M24L2.L2

public section

namespace CFSG.KC.M24L2

open CFSG.CGT.M24R CFSG.KC.Enum

@[expose] noncomputable def dC (i : Fin 3) : Nat := cwK (dWord10 i)

@[expose] noncomputable def thC (i : Fin 3) : Nat := cwK (thetaWord10 i)

@[expose] noncomputable def evK (u : Fin 3 → Nat) (w : List (Fin 3)) : Nat :=
  foldL (fun c k => mulC c (u k)) w idC

@[expose] noncomputable def normBK (x : Nat) : Bool := normKK [idC, b0C, b1C, b01C] b0C b1C x

@[expose] noncomputable def dTwin : BS (Fin 3) := bfsT 2048 (fun c => c) dC (List.finRange 3) idC

@[expose] noncomputable def thWordK (i : Fin 3) : List (Fin 3) :=
  (((dTwin.all.reverse.find? fun e => e.1 == thC i)).map Prod.snd).getD []

@[expose] noncomputable def dPart1K : Bool :=
  (List.finRange 3).all fun i => normBK (dC i) && normBK (thC i)

@[expose] noncomputable def dBody (c : Nat) : Bool :=
  bIf(normBK c, !(commK c (dC 0)) || !(commK c (dC 1)) || !(commK c (dC 2)) || Nat.beq c idC,
    true)

@[expose] noncomputable def dLin (m : Nat) : Bool :=
  commK (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) (Nat.shiftRight (dC 0) (nat_lit 4))) &&
  commK (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) (Nat.shiftRight (dC 1) (nat_lit 4))) &&
  commK (Nat.mul (nat_lit 16) m) (Nat.mul (nat_lit 16) (Nat.shiftRight (dC 2) (nat_lit 4)))

@[expose] noncomputable def dM (m : Nat) : Bool :=
  bIf(dLin m, allN 16 fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) fun c => dBody c, true)

@[expose] noncomputable def dE (E : List (Nat × Nat × Nat)) : Bool :=
  dM (nat_lit 33825) && allL (fun e => letN e.1 fun m => dM m) E

@[expose] noncomputable def dPart3K : Bool :=
  (List.finRange 3).all fun i =>
    Nat.beq (evK dC (thWordK i)) (thC i) && Nat.beq (evK thC (thWordK i)) (dC i)

end CFSG.KC.M24L2
