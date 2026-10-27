module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum

@[expose] noncomputable def getS (S : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => Nat.rec (motive := fun _ => Nat) x (fun i _ => ih i) j) S

@[expose] noncomputable def getLs (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun i _ => ih i) j) L

@[expose] noncomputable def depD (D p : Nat) : Nat := pg (nat_lit 8) (nat_lit 255) D p

@[expose] noncomputable def rowK (n w m : Nat) (S : List Nat) (k lv D b p d r : Nat) : Bool :=
  bIf(Nat.beq d (nat_lit 255), true,
    bIf(Nat.beq d (nat_lit 0), Nat.beq p b,
      strictB (Nat.land r (nat_lit 4095)) fun q => strictB (Nat.shiftRight r (nat_lit 12)) fun j =>
        bAnd(Nat.blt q n, bAnd(Nat.blt j k, bAnd(Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1),
          bAnd(Nat.beq (Nat.succ (depD D q)) d, Nat.beq (pg w m (getS S j) q) p))))))

@[expose] noncomputable def rowsFrom (n w m : Nat) (S : List Nat) (k lv D b cnt : Nat) (R : List Nat) :
    Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun p c => bAnd(Nat.beq p n, Nat.beq c cnt))
    (fun r _ ih p c => strictB (depD D p) fun d =>
      bAnd(rowK n w m S k lv D b p d r,
        strictB (Nat.succ p) fun p' => strictB (nIf(Nat.beq d (nat_lit 255), c, Nat.succ c)) fun c' =>
          ih p' c')) R

@[expose] noncomputable def rowsK (n w m : Nat) (S : List Nat) (k lv D b cnt : Nat) (R : List Nat) :
    Bool :=
  rowsFrom n w m S k lv D b cnt R (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def levelK (n w m : Nat) (S : List Nat) (k : Nat) (B K M D : List Nat)
    (R : List (List Nat)) (i : Nat) : Bool :=
  strictB (getS M i) fun lv => strictB (getS D i) fun d => strictB (getS B i) fun b =>
    strictB (getS K i) fun c => rowsK n w m S k lv d b c (getLs R i)

@[expose] noncomputable def lenS (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def prodL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 1) (fun x _ ih => Nat.mul x ih) L

@[expose] noncomputable def setL (L : List Nat) (i x : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun y t ih j => Nat.rec (motive := fun _ => List Nat) (List.cons x t)
      (fun j' _ => List.cons y (ih j')) j) L i

@[expose] noncomputable def fixLvK (w m : Nat) (S : List Nat) (k lv : Nat) (B : List Nat) (i : Nat) :
    Bool :=
  allN k fun j => bIf(Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1),
    allN i fun t => strictB (getS B t) fun x => Nat.beq (pg w m (getS S j) x) x, true)

end CFSG.KC.OrbRow

end
