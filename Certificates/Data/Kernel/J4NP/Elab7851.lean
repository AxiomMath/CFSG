module

public import Certificates.Data.Kernel.J4Loc.Trio

public section

namespace CFSG.KC.J4NP

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KC.Loop

@[expose] noncomputable def lnS (w P i : Nat) : Nat :=
  Nat.shiftRight (fld (Nat.add w (nat_lit 64)) P i) (nat_lit 64)

@[expose] noncomputable def keyT (t : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor x (Nat.shiftLeft ih (nat_lit 11))) t

@[expose] noncomputable def e11 : Nat := nat_lit 1298708349570020393652962442872833

@[expose] noncomputable def prodK (K K' : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => Nat.xor ih
      (Nat.mul (Nat.land (Nat.shiftRight K' k) e11) (fld (nat_lit 11) K k))) (nat_lit 11)

@[expose] noncomputable def idL : List Nat :=
  [nat_lit 1, nat_lit 2, nat_lit 4, nat_lit 8, nat_lit 16, nat_lit 32, nat_lit 64, nat_lit 128,
    nat_lit 256, nat_lit 512, nat_lit 1024]

@[expose] noncomputable def tabOK (t : List Nat) : Bool :=
  andB (Nat.beq (lenK t) (nat_lit 11)) (allL t fun v => Nat.blt v (nat_lit 2048))

@[expose] noncomputable def pinGo (KK : Nat) (TL : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 191))
    (fun t _ ih i => strictB i fun i => andB (tabOK t)
      (Bool.rec (motive := fun _ => Bool) (ih i)
        (andB (Nat.beq (lnS (nat_lit 121) KK i) (keyT t)) (ih (Nat.succ i)))
        (andB (notB (eqLK t idL)) (invK t)))) TL

@[expose] noncomputable def pinOK (KK : Nat) (TL : List (List Nat)) : Bool := pinGo KK TL (nat_lit 0)

@[expose] noncomputable def onesK (w : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)

@[expose] noncomputable def planeK (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) c) (bitB c j))) (nat_lit 2048)

@[expose] noncomputable def xpOK (XP : Nat) : Bool :=
  allR (nat_lit 11) fun j => Nat.beq (lnS (nat_lit 2048) XP j) (planeK j)

@[expose] noncomputable def outK (XP K i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.xor acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (lnS (nat_lit 2048) XP j) (bitB (fld (nat_lit 11) K j) i))) (nat_lit 11)

@[expose] noncomputable def fixK (XP K : Nat) : Nat :=
  Nat.xor (onesK (nat_lit 2048))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.xor (outK XP K i) (lnS (nat_lit 2048) XP i))) (nat_lit 11))

@[expose] noncomputable def pairOK (KK Ka Ca Pa x : Nat) : Bool :=
  strictB (lnS (nat_lit 121) KK x) fun Kx =>
    andB (notB (Nat.beq Ka Kx))
      (strictB (prodK Ka Kx) fun P => strictB (prodK Kx Ka) fun Q =>
        Bool.rec (motive := fun _ => Bool) (notB (Nat.beq P Q))
          (andB (Nat.beq P Q) (strictB (fld (nat_lit 8) Pa x) fun p =>
            andB (Nat.blt p (nat_lit 191)) (Nat.beq (lnS (nat_lit 121) KK p) P)))
          (bitB Ca x))

@[expose] noncomputable def rowOK (KK CMK PRK FMK XP : Nat) (FL : List (List Nat)) (a : Nat) : Bool :=
  strictB (lnS (nat_lit 121) KK a) fun Ka =>
    strictB (lnS (nat_lit 191) CMK a) fun Ca =>
      strictB (lnS (nat_lit 1528) PRK a) fun Pa =>
        strictB (lnS (nat_lit 2048) FMK a) fun Fa =>
          andB (notB (bitB Ca a))
            (andB (Nat.beq Fa (fixK XP Ka))
              (andB (subK Fa (keyK (rowL FL a)))
                (andB (Nat.ble (lenK (rowL FL a)) (nat_lit 128))
                  (allR (nat_lit 191) fun x =>
                    orB (Nat.beq x a) (pairOK KK Ka Ca Pa x)))))

@[expose] noncomputable def descK (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih ub => andB (Nat.blt x ub) (ih x)) L

@[expose] noncomputable def caK (CMK : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (onesK (nat_lit 191))
    (fun a _ ih => Nat.land ih (lnS (nat_lit 191) CMK a)) L

@[expose] noncomputable def lowK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ _ => onesK (Nat.succ x)) L

@[expose] noncomputable def chMask (Ch : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (Nat.land c (nat_lit 255)))) Ch

@[expose] noncomputable def imgK (Px : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (fld (nat_lit 8) Px a))) L

@[expose] noncomputable def childOK (MK PRK N m : Nat) (L : List Nat) (c : Nat) : Bool :=
  strictB (Nat.land c (nat_lit 255)) fun x => strictB (Nat.shiftRight c (nat_lit 8)) fun j =>
    andB (Nat.blt j N)
      (Nat.beq (lnS (nat_lit 191) MK j)
        (Nat.lor (Nat.lor m (Nat.shiftLeft (nat_lit 1) x)) (imgK (lnS (nat_lit 1528) PRK x) L)))

@[expose] noncomputable def chOK (MK CMK PRK N m : Nat) (L Ch : List Nat) : Bool :=
  strictB (caK CMK L) fun C =>
    andB (Nat.beq (chMask Ch) (Nat.sub C (Nat.land C (lowK L))))
      (allL Ch fun c => childOK MK PRK N m L c)

@[expose] noncomputable def andG (FMK : Nat) (G : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (onesK (nat_lit 2048))
    (fun g _ ih => Nat.land ih (lnS (nat_lit 2048) FMK g)) G

@[expose] noncomputable def bndOK (FMK m : Nat) (L G F : List Nat) : Bool :=
  orB (Nat.ble (lenK L) (nat_lit 7))
    (andB (allL G fun g => bitB m g)
      (andB (subK (andG FMK G) (keyK F))
        (Nat.ble (Nat.mul (lenK F) (Nat.succ (lenK L))) (nat_lit 1024))))

@[expose] noncomputable def entOK (MK CMK PRK FMK N i : Nat) (R : List (List Nat)) : Bool :=
  strictB (lnS (nat_lit 191) MK i) fun m =>
    andB (Nat.beq m (keyK (rowL R (nat_lit 0))))
      (andB (descK (rowL R (nat_lit 0)) (nat_lit 191))
        (andB (chOK MK CMK PRK N m (rowL R (nat_lit 0)) (rowL R (nat_lit 1)))
          (bndOK FMK m (rowL R (nat_lit 0)) (rowL R (nat_lit 2)) (rowL R (nat_lit 3)))))

@[expose] noncomputable def entGo (MK CMK PRK FMK N : Nat) (B : List (List (List Nat))) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun R _ ih i => strictB i fun i =>
      andB (orB (notB (Nat.blt i N)) (entOK MK CMK PRK FMK N i R)) (ih (Nat.succ i))) B

@[expose] noncomputable def blk4 (l : List (List (List (List Nat)))) (k : Nat) :
    List (List (List Nat)) :=
  List.rec (motive := fun _ => Nat → List (List (List Nat))) (fun _ => List.nil)
    (fun b _ ih k => Nat.rec (motive := fun _ => List (List (List Nat))) b (fun j _ => ih j) k) l k

@[expose] noncomputable def lenB (B : List (List (List Nat))) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) B

@[expose] noncomputable def entBlk (MK CMK PRK FMK N : Nat) (ENT : List (List (List (List Nat))))
    (k : Nat) : Bool :=
  andB (orB (Nat.beq (lenB (blk4 ENT k)) (nat_lit 32))
      (Nat.ble N (Nat.add (Nat.mul (nat_lit 32) k) (lenB (blk4 ENT k)))))
    (entGo MK CMK PRK FMK N (blk4 ENT k) (Nat.mul (nat_lit 32) k))

end CFSG.KC.J4NP

end
