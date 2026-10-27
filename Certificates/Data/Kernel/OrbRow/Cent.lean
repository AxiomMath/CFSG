module

public import Certificates.Data.Kernel.OrbRow.Defs
public import Certificates.Data.Kernel.PGrp
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp

@[expose] noncomputable def lettersK (k lv : Nat) (wd : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun j _ ih => bAnd(Nat.blt j k, bAnd(Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1), ih))) wd

@[expose] noncomputable def wordEqK (n w : Nat) (S : List Nat) (k lv x : Nat) (wd : List Nat) : Bool :=
  bAnd(lettersK k lv wd, Nat.beq x (posWordK n w (getS S) wd))

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) L

@[expose] noncomputable def fixSetK (n w m x : Nat) (F : List Nat) : Bool :=
  allN n (fun i => bIf(Nat.beq (pg w m x i) i, memK i F, bIf(memK i F, false, true)))

@[expose] noncomputable def actFK (w m x : Nat) (B img : List Nat) : Bool :=
  allN (lenS img) (fun t => Nat.beq (pg w m x (getS B t)) (getS B (getS img t)))

@[expose] noncomputable def lvCommK (n w m : Nat) (S : List Nat) (k lv x : Nat) : Bool :=
  allN k (fun j => bIf(Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1), commOK n w m (getS S j) x, true))

@[expose] noncomputable def powIdK (n w m x e : Nat) : Bool :=
  allN n (fun i => Nat.beq (fpow (pg w m x) e i) i)

@[expose] noncomputable def movesK (n w m x : Nat) : Bool :=
  bIf(allN n (fun i => Nat.beq (pg w m x i) i), false, true)

@[expose] noncomputable def subKey (w : Nat) (B : List Nat) (off nf : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t ih => Nat.lor ih (Nat.shiftLeft (getS B (Nat.add off t)) (Nat.mul w t))) nf

@[expose] noncomputable def mapKey (w m g nf key : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t ih => Nat.lor ih (Nat.shiftLeft (pg w m g fld(key, Nat.mul w t, m)) (Nat.mul w t))) nf

@[expose] noncomputable def conjKey (w m x xi g : Nat) (B : List Nat) (off nf : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t ih => Nat.lor ih (Nat.shiftLeft
      (pg w m x (pg w m g (pg w m xi (getS B (Nat.add off t))))) (Nat.mul w t))) nf

@[expose] noncomputable def normK (n w m : Nat) (G : Nat → Nat) (k x : Nat) (B : List Nat)
    (off nf : Nat) (RK : List Nat) : Bool :=
  strictB (CFSG.KS.pinvS n w m x) fun xi =>
    bAnd(permOK n w m (Nat.mul n w) x xi,
      allN k (fun j => memK (conjKey w m x xi (G j) B off nf) RK))

@[expose] noncomputable def recDep (fw r : Nat) : Nat := fld(r, Nat.add fw (nat_lit 8), nat_lit 255)

@[expose] noncomputable def recK (act : Nat → Nat → Nat) (k fw fm root cnt : Nat) (E RR : List Nat)
    (e r : Nat) : Bool :=
  strictB (Nat.land r fm) fun par => strictB fld(r, fw, nat_lit 255) fun j =>
  strictB (recDep fw r) fun d =>
    bAnd(bIf(Nat.beq d (nat_lit 0), Nat.beq e root,
        bAnd(Nat.blt par cnt, bAnd(Nat.blt j k,
          bAnd(Nat.beq (Nat.succ (recDep fw (getS RR par))) d, Nat.beq e (act j (getS E par)))))),
      allN k (fun l => strictB fld(r, Nat.add (Nat.add fw (nat_lit 16)) (Nat.mul fw l), fm) fun q =>
        bAnd(Nat.blt q cnt, Nat.beq (getS E q) (act l e))))

@[expose] noncomputable def recsFrom (act : Nat → Nat → Nat) (ord : Nat → Nat) (k fw fm root cnt : Nat)
    (E RR : List Nat) (Es : List Nat) : List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Nat → Bool)
    (fun Rs i _ => bAnd(Nat.beq i cnt, List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Rs))
    (fun e _ ih Rs i prev => List.rec (motive := fun _ => Bool) false
      (fun r Rt _ => strictB (ord e) fun oe =>
        bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt prev oe),
        bAnd(recK act k fw fm root cnt E RR e r, strictB (Nat.succ i) fun i' => ih Rt i' oe))) Rs)
    Es

@[expose] noncomputable def orbRecK (act : Nat → Nat → Nat) (ord : Nat → Nat) (k fw fm root cnt : Nat)
    (E RR : List Nat) : Bool :=
  recsFrom act ord k fw fm root cnt E RR E RR (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def revKey (w m nf key : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t ih => Nat.lor (Nat.shiftLeft ih w) fld(key, Nat.mul w t, m)) nf

@[expose] noncomputable def invsF (n w m : Nat) (S : List Nat) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun c => c List.nil)
    (fun s _ ih c => strictB (CFSG.KS.pinvS n w m s) fun si => ih (fun L => c (List.cons si L))) S

@[expose] noncomputable def ncAllK (n w m idn : Nat) (G : Nat → Nat) (k : Nat) (TE : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(bIf(Nat.beq e idn, true,
      bIf(allN k (fun j => commOK n w m e (G j)), false, true)), ih)) TE

end CFSG.KC.OrbRow

end
