module

public import Certificates.Data.Kernel.OrbRow.Cent

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp

@[expose] noncomputable def movLvK (w m : Nat) (S : List Nat) (k lv lo : Nat) (F : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(bIf(Nat.blt p lo, true,
      bIf(allN k (fun j => bIf(Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1),
        Nat.beq (pg w m (getS S j) p) p, true)), false, true)), ih)) F

@[expose] noncomputable def invPow (o : Nat → Nat) (wd : List (Nat × Bool)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun l _ ih => Bool.rec (motive := fun _ => List Nat)
      (List.replicate (Nat.sub (o l.1) 1) l.1 ++ ih) (List.cons l.1 ih) l.2) wd

@[expose] noncomputable def relK (n w : Nat) (S : List Nat) (o : Nat → Nat)
    (ws : List (List (Nat × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun wd _ ih => bAnd(Nat.beq (posWordK n w (getS S) (invPow o wd)) (pidn n w), ih)) ws

end CFSG.KC.OrbRow

end
