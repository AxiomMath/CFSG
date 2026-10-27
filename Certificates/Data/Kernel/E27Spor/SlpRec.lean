module

public import Certificates.Data.Kernel.E27Spor.OrbRec

public section

namespace CFSG.KC.E27Spor

open CFSG.KC.Enum CFSG.Monster.B.Pinned

@[expose] noncomputable def mkL (f : Nat → List Nat) (n : Nat) : Nat → List (List Nat) :=
  Nat.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun _ ih s => List.cons (f s) (ih (Nat.succ s))) n

@[expose] noncomputable def rowsR (d : Nat) (R : Nat → Nat) (k : Nat) : List (List Nat) :=
  mkL (fun r => decD d (R (Nat.add (Nat.mul d k) r))) d (nat_lit 0)

@[expose] noncomputable def nthM (L : List (List (List Nat))) (k : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun x _ ih j => Nat.rec (motive := fun _ => List (List Nat)) x (fun j' _ => ih j') j) L k

@[expose] noncomputable def nthR (L : List (List Nat)) (r : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun j' _ => ih j') j) L r

@[expose] noncomputable def slpAt (d : Nat) (base : List (List (List Nat))) (nb : Nat)
    (R A B : Nat → Nat) (k : Nat) : Bool :=
  bIf(Nat.blt k nb,
    allN d fun r => Nat.beq (R (Nat.add (Nat.mul d k) r)) (lcode (nthR (nthM base k) r)),
    bAnd(Nat.blt (A k) k, bAnd(Nat.blt (B k) k,
      allN d fun r => Nat.beq (R (Nat.add (Nat.mul d k) r))
        (lcode (lvecMul 3 d (decD d (R (Nat.add (Nat.mul d (A k)) r))) (rowsR d R (B k)))))))

end CFSG.KC.E27Spor

end
