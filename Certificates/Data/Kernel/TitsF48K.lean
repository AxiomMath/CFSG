module

public import Certificates.Data.Kernel.TitsDK

public section

namespace CFSG.KC.TitsF48K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK

@[expose] noncomputable def sgR (FA : Nat → Nat) (PR LB k kp : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => k)
    (fun _ ih j => nIf(Nat.beq (fw (nat_lit 4) LB j) (nat_lit 15),
      nIf(Nat.blt j (nat_lit 512), k, kp),
      strictN (ih (fw (nat_lit 12) PR j)) (fun y => gp (FA (fw (nat_lit 4) LB j)) y)))

@[expose] noncomputable def fiR (FAI : Nat → Nat) (PR LB : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
    (fun _ ih j v => nIf(Nat.beq (fw (nat_lit 4) LB j) (nat_lit 15), v,
      strictN (gp (FAI (fw (nat_lit 4) LB j)) v) (fun w => ih (fw (nat_lit 12) PR j) w)))

@[expose] noncomputable def sF (FA : Nat → Nat) (LAY PR LB PS k kp x : Nat) : Nat :=
  nIf(Nat.blt x (nat_lit 1755), nIf(Nat.ble (layAt LAY x) (nat_lit 6), x,
    strictN (fw (nat_lit 13) PS x) (fun j => sgR FA PR LB k kp (Nat.succ j) j)), nat_lit 8191)

@[expose] noncomputable def sH (FA : Nat → Nat) (LAY PR LB PS : Nat) (part : Bool) (kv x : Nat) :
    Nat :=
  nIf(Nat.blt x (nat_lit 1755), nIf(Nat.ble (layAt LAY x) (nat_lit 6), x,
    strictN (fw (nat_lit 13) PS x) (fun j =>
      nIf(bIf(part, Nat.blt j (nat_lit 512), Nat.ble (nat_lit 512) j),
        sgR FA PR LB kv kv (Nat.succ j) j, nat_lit 8191))), nat_lit 8191)

@[expose] noncomputable def gpS (a x : Nat) : Nat := nIf(Nat.blt x (nat_lit 1755), gp a x, nat_lit 8191)

@[expose] noncomputable def itP (g : Nat → Nat) (o x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => strictN ih g) o

@[expose] noncomputable def witS (nG q0 b1 b2 : Nat) (s : Nat → Nat) (r : List Nat) (full : Bool) :
    Bool :=
  strictB (r.getD (nat_lit 1) (nat_lit 0)) (fun a => strictB (r.getD (nat_lit 2) (nat_lit 0)) (fun c =>
  bIf(Nat.beq (r.headD (nat_lit 0)) (nat_lit 1), bAnd(Nat.blt a (nat_lit 1755),
      strictB (gpS nG (s (gpS nG (s a)))) (fun y =>
        bAnd(Nat.blt y (nat_lit 1755), bIf(Nat.beq y a, false, true)))),
  bIf(Nat.beq (r.headD (nat_lit 0)) (nat_lit 3), bAnd(Nat.blt a (nat_lit 2), bAnd(Nat.blt c (nat_lit 1755),
      strictB (itP (fun y => gpS nG (s (gpS (nIf(Nat.beq a (nat_lit 0), b1, b2)) y)))
          (nIf(Nat.beq a (nat_lit 0), nat_lit 4, nat_lit 5)) c)
        (fun y => bAnd(Nat.blt y (nat_lit 1755), bIf(Nat.beq y c, false, true))))),
  bAnd(full, bAnd(Nat.beq (r.headD (nat_lit 0)) (nat_lit 2), bAnd(Nat.blt a (nat_lit 1755),
    bAnd(Nat.blt (nat_lit 0) c, bAnd(bIf(Nat.beq (Nat.mod (nat_lit 17971200) c) (nat_lit 0), false, true),
      cycFrom (fun y => gp nG (s (gp q0 y))) a (Nat.sub c (nat_lit 1))
        (gp nG (s (gp q0 a))))))))))))

@[expose] noncomputable def rowA (FA FAI : Nat → Nat) (LAY ORD PR LB PS nG q0 b1 b2 : Nat)
    (S1 : List Nat) (i : Nat) (r : List Nat) : Bool :=
  strictB (fw (nat_lit 13) ORD i) (fun k =>
  bIf(Nat.blt i (nat_lit 512),
    bIf(Nat.beq (r.headD (nat_lit 0)) (nat_lit 0),
      bAnd(Nat.blt (r.getD (nat_lit 1) (nat_lit 0)) (nat_lit 16),
        Nat.beq (S1.getD (r.getD (nat_lit 1) (nat_lit 0)) (nat_lit 0)) i),
      witS nG q0 b1 b2 (sH FA LAY PR LB PS true k) r false),
    strictB (gp nG k) (fun y => strictB (fw (nat_lit 13) PS y) (fun j =>
      bAnd(Nat.ble (nat_lit 512) j, bAnd(Nat.blt j (nat_lit 1024), bAnd(Nat.beq (fw (nat_lit 13) ORD j) y,
        strictB (fiR FAI PR LB (Nat.succ j) j (gp nG (nat_lit 87))) (fun kp =>
          witS nG q0 b1 b2 (sF FA LAY PR LB PS k kp) r true))))))))

@[expose] noncomputable def rowB (FA FAI : Nat → Nat) (LAY ORD PR LB PS nG q0 b1 b2 : Nat)
    (S2 : List Nat) (i : Nat) (r : List Nat) : Bool :=
  strictB (fw (nat_lit 13) ORD i) (fun kp =>
  bIf(Nat.ble (nat_lit 512) i,
    bIf(Nat.beq (r.headD (nat_lit 0)) (nat_lit 0),
      bAnd(Nat.blt (r.getD (nat_lit 1) (nat_lit 0)) (nat_lit 16),
        Nat.beq (S2.getD (r.getD (nat_lit 1) (nat_lit 0)) (nat_lit 0)) i),
      witS nG q0 b1 b2 (sH FA LAY PR LB PS false kp) r false),
    strictB (gp nG kp) (fun y => strictB (fw (nat_lit 13) PS y) (fun j =>
      bAnd(Nat.blt j (nat_lit 512), bAnd(Nat.beq (fw (nat_lit 13) ORD j) y,
        strictB (fiR FAI PR LB (Nat.succ j) j (gp nG (nat_lit 133))) (fun k =>
          witS nG q0 b1 b2 (sF FA LAY PR LB PS k kp) r true)))))))

@[expose] noncomputable def rowC (FA : Nat → Nat) (LAY ORD PR LB PS nG q0 b1 b2 : Nat)
    (S1 S2 : List Nat) (i : Nat) (r : List Nat) : Bool :=
  strictB (fw (nat_lit 13) ORD (S1.getD (Nat.div i (nat_lit 16)) (nat_lit 0))) (fun k =>
  strictB (fw (nat_lit 13) ORD (S2.getD (Nat.mod i (nat_lit 16)) (nat_lit 0))) (fun kp =>
  bIf(Nat.beq (r.headD (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq k (nat_lit 87), Nat.beq kp (nat_lit 133)),
    witS nG q0 b1 b2 (sF FA LAY PR LB PS k kp) r true)))

@[expose] noncomputable def rowsK (f : Nat → List Nat → Bool) (i₀ : Nat) (R : List (List Nat)) :
    Bool :=
  allL (fun i r => f (Nat.add i₀ i) r) R (nat_lit 0)

@[expose] noncomputable def halfF (ORD PR LB : Nat) : Bool :=
  allN (nat_lit 1024) (fun i => bIf(Nat.beq (fw (nat_lit 4) LB i) (nat_lit 15),
    Nat.beq (fw (nat_lit 13) ORD i) (nIf(Nat.blt i (nat_lit 512), nat_lit 87, nat_lit 133)),
    bIf(Nat.blt i (nat_lit 512), true, Nat.ble (nat_lit 512) (fw (nat_lit 12) PR i))))

@[expose] noncomputable def invF (FA FAI : Nat → Nat) : Bool :=
  allN (nat_lit 6) (fun j => strictB (FA j) (fun a => strictB (FAI j) (fun ai =>
    allN (nat_lit 1755) (fun x => Nat.beq (gp ai (gp a x)) x))))

@[expose] noncomputable def smallF (lp FA : Nat → Nat) (PL nG t b1 b2 : Nat) : Bool :=
  bAnd(allN (nat_lit 1755) (fun x => Nat.beq (gp nG (gp nG x)) x),
  bAnd(allN (nat_lit 6) (fun j => strictB (FA j) (fun a =>
    bAnd(lineMap lp (gp a) 0 0, lineMap lp (fun x => gp nG (gp a (gp nG x))) 0 0))),
  bAnd(lineMap lp (gp t) 0 0, bAnd(lineMap lp (gp b1) 0 0, bAnd(lineMap lp (gp b2) 0 0,
  bAnd(allN (nat_lit 1755) (fun x => Nat.beq (itP (fun y => gp nG (gp b1 y)) (nat_lit 4) x) x),
  bAnd(allN (nat_lit 1755) (fun x => Nat.beq (itP (fun y => gp nG (gp b2 y)) (nat_lit 5) x) x),
  bAnd(allN (nat_lit 5) (fun k => strictB (plK PL 0 k) (fun v => bIf(Nat.beq v 0, true,
    anyN (nat_lit 4) (fun i => lineMap lp (tn1 t nG i) 0 v)))),
    allN (nat_lit 1755) (fun p => bIf(Nat.beq p 0, true, bIf(Nat.beq (gp t p) p,
      anyN (nat_lit 6) (fun j => bIf(Nat.beq (gp (FA j) p) p, false, true)), true)))))))))))

end CFSG.KC.TitsF48K

end
