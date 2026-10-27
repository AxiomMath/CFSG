module

public import Certificates.Data.Kernel.U6.Core
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.KC.Enum (pcomp)

@[expose] noncomputable def pc (p q : Nat) : Nat :=
  strictN p fun p => strictN q fun q => pcomp (nat_lit 693) (nat_lit 10) (nat_lit 1023) p q

@[expose] noncomputable def ID693 : Nat :=
  sumBelow (nat_lit 693) (nat_lit 11) fun i => Nat.shiftLeft i (Nat.mul (nat_lit 10) i)

@[expose] noncomputable def wordK (LT : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ID693 (fun k _ ih => pc (letK LT k) ih) w

@[expose] noncomputable def fixK (P : Nat) : Nat :=
  strictN P fun P => sumBelow (nat_lit 693) (nat_lit 11) fun p =>
    nIf(Nat.beq (ap10 P p) p, nat_lit 1, nat_lit 0)

@[expose] noncomputable def invP (P : Nat) : Nat :=
  strictN P fun P => sumBelow (nat_lit 693) (nat_lit 11) fun i =>
    Nat.shiftLeft i (Nat.mul (nat_lit 10) (ap10 P i))

@[expose] noncomputable def elt (S i : Nat) : Nat := fget S i (nat_lit 6930)

@[expose] noncomputable def evW (S : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ID693
    (fun c _ ih => pc (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
      elt S (Nat.shiftRight c (nat_lit 1)), invP (elt S (Nat.shiftRight c (nat_lit 1))))) ih) w

@[expose] noncomputable def evList (S : Nat) (ws : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun w _ ih i => strictN (evW S w) fun P =>
      Nat.lor (Nat.shiftLeft P (Nat.mul (nat_lit 6930) i)) (ih (Nat.succ i))) ws (nat_lit 0)

@[expose] noncomputable def conjP (g x : Nat) : Nat := pc (pc g x) (invP g)

@[expose] noncomputable def check3142 (LT : Nat) (aW : List (List Nat)) : Bool :=
  strictB (evList LT aW) fun A =>
    andB (Nat.beq (fixK (elt A (nat_lit 2))) (nat_lit 181))
      (Nat.beq (fixK (evW A [nat_lit 0, nat_lit 2, nat_lit 8, nat_lit 4])) (nat_lit 21))

end CFSG.KC.U6

end
