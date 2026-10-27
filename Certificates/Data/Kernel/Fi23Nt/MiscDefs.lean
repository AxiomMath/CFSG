module

public import Certificates.Data.Kernel.Fi23K.Defs
public import Certificates.Data.Kernel.Fi23R.Defs

public section

namespace CFSG.KC.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R

@[expose] noncomputable def cwK (G : Nat → Nat) (u v : List Nat) (t : Nat) : Bool :=
  Nat.beq (wv G u (wv G v t)) (wv G v (wv G u t))

@[expose] noncomputable def cbK (G : Nat → Nat) (C B : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun b _ ih2 => bAnd(allN (nat_lit 6) (cwK G c b), ih2)) B, ih)) C

@[expose] noncomputable def t2K0 (G : Nat → Nat) (x : Nat) : Nat :=
  tA G (nat_lit 0) (tA G (nat_lit 1) (tA G (nat_lit 39) x))

@[expose] noncomputable def t2K (G : Nat → Nat) (Q : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => bAnd(allN (nat_lit 6) (fun t =>
      Nat.beq (wv G w (t2K0 G t)) (t2K0 G (wv G w t))), ih)) Q

@[expose] noncomputable def hyK (G : Nat → Nat) (h : List Nat) (v0 : Nat) (Y : List (List Nat)) :
    Bool :=
  bAnd(Nat.beq (wv G h v0) (nat_lit 0),
    allN (nat_lit 6) fun t => Nat.beq (wv G h (wv G (List.getD Y t []) v0)) t)

@[expose] noncomputable def ddiffK (G : Nat → Nat) (p q x : Nat) : Bool :=
  Bool.not (Nat.beq (tA G p (tA G q (tA G (nat_lit 0) (tA G (nat_lit 1) x))))
    (tA G (nat_lit 0) (tA G (nat_lit 1) (tA G p (tA G q x)))))

@[expose] noncomputable def pairsK (G : Nat → Nat) (F X : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun q _ ih2 => bAnd(bIf(Nat.beq p q, true,
        bIf(bAnd(Nat.ble p (nat_lit 1), Nat.ble q (nat_lit 1)), true,
          bIf(Nat.beq (tA G p q) q,
            List.rec (motive := fun _ => Bool) false
              (fun x _ ih3 => bIf(ddiffK G p q x, true, ih3)) X, true))), ih2)) F, ih)) F

end CFSG.KC.Fi23Nt

end
