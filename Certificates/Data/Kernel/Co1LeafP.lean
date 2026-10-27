module

public import Certificates.Data.Kernel.Co1Three.Leaf

public section

namespace CFSG.KC.Co1LeafP

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.Co1BBound
  CFSG.KC.Co1Leaf

@[expose] noncomputable def getLP (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun a _ ih i => Nat.rec (motive := fun _ => List Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def getLLP (L : List (List (List Nat))) : Nat → List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun a _ ih i => Nat.rec (motive := fun _ => List (List Nat)) a (fun j _ => ih j) i) L

@[expose] noncomputable def bitN (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) b

@[expose] noncomputable def actK (BT : List Nat) (s v : Nat) : Nat := vmF (nat_lit 24) (getL (nat_lit 0) BT s) v

@[expose] noncomputable def slotU (BT U : List Nat) (c : Nat) : Nat :=
  actK BT (Nat.mod c (nat_lit 32)) (getL (nat_lit 0) U (Nat.div c (nat_lit 32)))

@[expose] noncomputable def sumU (BT U : List Nat) (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun c _ ih => Nat.xor (slotU BT U c) ih) cs

@[expose] noncomputable def slotP (IMS : List (List (List Nat))) (P : List Nat) (c : Nat) : Nat :=
  selK (getLP (getLLP IMS (Nat.div c (nat_lit 32))) (Nat.mod c (nat_lit 32)))
    (getL (nat_lit 0) P (Nat.div c (nat_lit 32)))

@[expose] noncomputable def sumP (IMS : List (List (List Nat))) (P : List Nat) (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun c _ ih => Nat.xor (slotP IMS P c) ih) cs

@[expose] noncomputable def codesOK (nb i : Nat) (cs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => andB (Nat.ble (Nat.div c (nat_lit 32)) i)
      (andB (Nat.blt (Nat.mod c (nat_lit 32)) nb) ih)) cs

@[expose] noncomputable def testsUK (XB : Nat → Nat) (BT U : List Nat) (i : Nat) (T : List (List Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ ih => andB (codesOK (lenL BT) i (List.tail t))
      (andB (Nat.beq (bitN (memK XB (sumU BT U (List.tail t)))) (List.headD t (nat_lit 2))) ih)) T

@[expose] noncomputable def ltK (E : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (Nat.blt e (pw2 (nat_lit 24))) ih) E

@[expose] noncomputable def imgsK (BT E : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun b _ ih => List.cons (List.rec (motive := fun _ => List Nat) List.nil
      (fun e _ ih2 => strictL (vmF (nat_lit 24) b e) fun v => List.cons v ih2) E) ih) BT

@[expose] noncomputable def eqLL : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | a :: as, b :: bs => andB (eqL a b) (eqLL as bs)
  | _, _ => false
where
  eqL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => andB (Nat.beq a b) (eqL as bs)
  | _, _ => false

@[expose] noncomputable def levelOK (XB : Nat → Nat) (BT U : List Nat) (i : Nat) (E : List Nat) (m u : Nat)
    (T : List (List Nat)) (IM : List (List Nat)) : Bool :=
  strictB (selK BT m) fun eT =>
    andB (ltK E) (andB (allN (nat_lit 24) fun r => strictB (fget eT r (nat_lit 24)) fun x =>
      Nat.beq (selK E (crdK E x)) x)
    (andB (Nat.beq (vmF (nat_lit 24) eT u) u) (andB (memK XB u)
    (andB (testsUK XB BT U i T) (eqLL IM (imgsK BT E))))))

@[expose] noncomputable def levelsOK (XB : Nat → Nat) (BT U : List Nat) (IMS : List (List (List Nat))) :
    List (List Nat) → List Nat → List Nat → List (List (List Nat)) → Nat → Bool
  | E :: Es, m :: Ms, u :: Us, T :: Ts, i =>
    andB (levelOK XB BT U i E m u T (getLLP IMS i)) (levelsOK XB BT U IMS Es Ms Us Ts (Nat.succ i))
  | [], [], [], [], _ => true
  | _, _, _, _, _ => false

@[expose] noncomputable def packU (BT U SL : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun c _ ih r => Nat.lor (Nat.shiftLeft (slotU BT U c) (Nat.mul (nat_lit 24) r)) (ih (Nat.succ r)))
    SL (nat_lit 0)

@[expose] noncomputable def passPK (XB : Nat → Nat) (IMS : List (List (List Nat))) (P : List Nat) (x : Nat)
    (T : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ ih => andB (Nat.beq (bitN (memK XB (sumP IMS (List.append P (List.cons x List.nil))
      (List.tail t)))) (List.headD t (nat_lit 2))) ih) T

@[expose] noncomputable def candPK (XB : Nat → Nat) (IMS : List (List (List Nat))) (E : List Nat)
    (T : List (List Nat)) (P : List Nat) (acc : List (List Nat)) : Nat → List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat)) acc
    (fun x ih => Bool.rec (motive := fun _ => List (List Nat)) ih
      (List.cons (List.append P (List.cons x List.nil)) ih)
      (andB (memK XB (selK E x)) (passPK XB IMS P x T)))

@[expose] noncomputable def stepPK (XB : Nat → Nat) (IMS : List (List (List Nat))) (E : List Nat)
    (T : List (List Nat)) (Ps : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun P _ ih => candPK XB IMS E T P ih (pw2 (lenL E))) Ps

@[expose] noncomputable def searchPK (XB : Nat → Nat) (IMS : List (List (List Nat))) :
    List (List Nat) → List (List (List Nat)) → List (List Nat) → List (List Nat)
  | E :: Es, T :: Ts, Ps => searchPK XB IMS Es Ts (stepPK XB IMS E T Ps)
  | _, _, Ps => Ps

@[expose] noncomputable def lenLL (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def leafPK (XB : Nat → Nat) (BT : List Nat) (Es : List (List Nat)) (Ms U : List Nat)
    (Ts : List (List (List Nat))) (IMS : List (List (List Nat))) (SL : List Nat) (UIT N : Nat) : Bool :=
  andB (Nat.blt (lenL BT) (nat_lit 33)) (andB (levelsOK XB BT U IMS Es Ms U Ts (nat_lit 0))
    (andB (Nat.beq (lenL SL) (nat_lit 24)) (andB (codesOK (lenL BT) (Nat.sub (lenL U) (nat_lit 1)) SL)
    (andB (Nat.beq (mulWK UIT (packU BT U SL)) oneK)
      (Nat.beq (lenLL (searchPK XB IMS Es Ts (List.cons List.nil List.nil))) N)))))

end CFSG.KC.Co1LeafP

end
