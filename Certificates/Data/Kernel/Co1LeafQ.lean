module

public import Certificates.Data.Kernel.Co1LeafP

public section

namespace CFSG.KC.Co1LeafQ

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.Co1BBound
  CFSG.KC.Co1Leaf CFSG.KC.Co1LeafP

@[expose] noncomputable def imgQ (IM : List (List Nat)) (x : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun L _ ih => strictL (selK L x) fun v => List.cons v ih) IM

@[expose] noncomputable def candsN (XB : Nat → Nat) (E : List Nat) (IM : List (List Nat)) (n : Nat) :
    List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat)) List.nil
    (fun x ih => Bool.rec (motive := fun _ => List (List Nat)) ih (List.cons (imgQ IM x) ih)
      (memK XB (selK E x))) n

@[expose] noncomputable def candsQ (XB : Nat → Nat) (E : List Nat) (IM : List (List Nat)) :
    List (List Nat) :=
  candsN XB E IM (pw2 (lenL E))

@[expose] noncomputable def slotQ (P : List (List Nat)) (c : Nat) : Nat :=
  getL (nat_lit 0) (getLP P (Nat.div c (nat_lit 32))) (Nat.mod c (nat_lit 32))

@[expose] noncomputable def sumQ (P : List (List Nat)) (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun c _ ih => Nat.xor (slotQ P c) ih) cs

@[expose] noncomputable def strictLL (y : Nat) (k : Nat → List (List Nat)) : List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat)) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def prepQ (P : List (List Nat)) (T : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun t _ ih => strictLL (sumQ P (List.tail (List.tail t))) fun F =>
      List.cons (List.cons (List.headD t (nat_lit 2))
        (List.cons (List.headD (List.tail t) (nat_lit 0)) (List.cons F List.nil))) ih) T

@[expose] noncomputable def passQ (XB : Nat → Nat) (R : List (List Nat)) (C : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (Nat.beq (bitN (memK XB (Nat.xor (getL (nat_lit 0) r (nat_lit 2))
      (selK C (getL (nat_lit 0) r (nat_lit 1)))))) (getL (nat_lit 0) r (nat_lit 0))) ih) R

@[expose] noncomputable def candQ (XB : Nat → Nat) (R P : List (List Nat)) (CL : List (List Nat))
    (acc : List (List (List Nat))) : List (List (List Nat)) :=
  List.rec (motive := fun _ => List (List (List Nat))) acc
    (fun C _ ih => Bool.rec (motive := fun _ => List (List (List Nat))) ih
      (List.cons (List.append P (List.cons C List.nil)) ih) (passQ XB R C)) CL

@[expose] noncomputable def stepQ (XB : Nat → Nat) (CL : List (List Nat)) (T : List (List Nat))
    (Ps : List (List (List Nat))) : List (List (List Nat)) :=
  List.rec (motive := fun _ => List (List (List Nat))) List.nil
    (fun P _ ih => candQ XB (prepQ P T) P CL ih) Ps

@[expose] noncomputable def searchQ (XB : Nat → Nat) :
    List (List (List Nat)) → List (List (List Nat)) → List (List (List Nat)) → List (List (List Nat))
  | CL :: CLs, T :: Ts, Ps => searchQ XB CLs Ts (stepQ XB CL T Ps)
  | _, _, Ps => Ps

@[expose] noncomputable def lenQ (L : List (List (List Nat))) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def maskCodes (i S : Nat) (cs : List Nat) (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) cs
    (fun s ih => Bool.rec (motive := fun _ => List Nat) ih
      (List.cons (Nat.add (Nat.mul (nat_lit 32) i) s) ih) (bit S s)) n

@[expose] noncomputable def convQ (nb i : Nat) (T : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun t _ ih => List.cons (List.cons (List.headD t (nat_lit 2))
      (maskCodes i (List.headD (List.tail t) (nat_lit 0)) (List.tail (List.tail t)) nb)) ih) T

@[expose] noncomputable def fixK (nb i : Nat) (cs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => andB (Nat.blt (Nat.div c (nat_lit 32)) i)
      (andB (Nat.blt (Nat.mod c (nat_lit 32)) nb) ih)) cs

@[expose] noncomputable def fixQ (nb i : Nat) (T : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ ih => andB (Nat.blt (List.headD (List.tail t) (pw2 nb)) (pw2 nb))
      (andB (fixK nb i (List.tail (List.tail t))) ih)) T

@[expose] noncomputable def levelQ (XB : Nat → Nat) (BT U : List Nat) (i : Nat) (E : List Nat) (m u : Nat)
    (T : List (List Nat)) (IM CL : List (List Nat)) : Bool :=
  andB (levelOK XB BT U i E m u (convQ (lenL BT) i T) IM)
    (andB (fixQ (lenL BT) i T) (eqLL CL (candsQ XB E IM)))

@[expose] noncomputable def levelsQ (XB : Nat → Nat) (BT U : List Nat) (IMS : List (List (List Nat))) :
    List (List Nat) → List Nat → List Nat → List (List (List Nat)) → List (List (List Nat)) → Nat →
      Bool
  | E :: Es, m :: Ms, u :: Us, T :: Ts, CL :: CLs, i =>
    andB (levelQ XB BT U i E m u T (getLLP IMS i) CL)
      (levelsQ XB BT U IMS Es Ms Us Ts CLs (Nat.succ i))
  | [], [], [], [], [], _ => true
  | _, _, _, _, _, _ => false

@[expose] noncomputable def leafQK (XB : Nat → Nat) (BT : List Nat) (Es : List (List Nat)) (Ms U : List Nat)
    (Ts : List (List (List Nat))) (IMS CLs : List (List (List Nat))) (SL : List Nat) (UIT N : Nat) :
    Bool :=
  andB (Nat.blt (lenL BT) (nat_lit 33)) (andB (levelsQ XB BT U IMS Es Ms U Ts CLs (nat_lit 0))
    (andB (Nat.beq (lenL SL) (nat_lit 24)) (andB (codesOK (lenL BT) (Nat.sub (lenL U) (nat_lit 1)) SL)
    (andB (Nat.beq (mulWK UIT (packU BT U SL)) oneK)
      (Nat.beq (lenQ (searchQ XB CLs Ts (List.cons List.nil List.nil))) N)))))

end CFSG.KC.Co1LeafQ

end
