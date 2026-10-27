module

public import Certificates.Data.Kernel.Misc.O73

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73

@[expose] noncomputable def idxN (L : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Bool.rec (motive := fun _ => Nat) (Nat.succ ih) 0 (Nat.beq x c)) L

@[expose] noncomputable def ptK (L : List Nat) (nm f : Nat → Nat) (y : Nat) : Nat :=
  idxN L (nm (f (L.getD y 0)))

@[expose] noncomputable def liftAt (L : List Nat) (nm dl fr : Nat → Nat) (P SG RT : List Nat)
    (k : Nat) : Bool :=
  let x := P.getD k 0
  let D := ptK L nm dl
  let F := ptK L nm fr
  Nat.blt (at' 5 (RT.getD 0 0) k) 21 && Nat.blt (at' 5 (RT.getD 1 0) k) 21 &&
    Nat.blt (at' 5 (RT.getD 2 0) k) 21 && Nat.blt (at' 5 (RT.getD 3 0) k) 21 &&
    Nat.beq (SG.getD k 0) (at' 5 (RT.getD 0 0) k) &&
    Nat.beq (F x) (P.getD (at' 5 (RT.getD 1 0) k) 0) &&
    Nat.beq (D (F (D (D x)))) (P.getD (at' 5 (RT.getD 2 0) k) 0) &&
    Nat.beq (D (D (F (D x)))) (P.getD (at' 5 (RT.getD 3 0) k) 0)

@[expose] noncomputable def liftK (L : List Nat) (nm dl fr : Nat → Nat) (P SG RT : List Nat) :
    Bool :=
  Nat.beq RT.length 4 && Nat.rec (motive := fun _ => Bool) true
    (fun k acc => acc && liftAt L nm dl fr P SG RT k) 21

end CFSG.SmithE.K
