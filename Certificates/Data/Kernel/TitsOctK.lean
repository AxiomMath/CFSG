module

public import Certificates.Data.Kernel.TwoF4LieK

public section

namespace CFSG.KC.TitsOctK

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK

@[expose] noncomputable def fw (w a i : Nat) : Nat := pg w (mask w) a i

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  bIf(allN n (fun i => bIf(f i, false, true)), false, true)

@[expose] noncomputable def plK (PL x k : Nat) : Nat :=
  fw (nat_lit 12) PL (Nat.add (Nat.mul (nat_lit 5) x) k)

@[expose] noncomputable def nbK (lp : Nat → Nat) (PL x k : Nat) : Nat :=
  nIf(Nat.blt x (nat_lit 1755), Nat.add (plK PL x k) (nat_lit 1755),
    lp (Nat.add (Nat.mul (nat_lit 3) (Nat.sub x (nat_lit 1755))) k))

@[expose] noncomputable def degK (x : Nat) : Nat :=
  nIf(Nat.blt x (nat_lit 1755), nat_lit 5, nat_lit 3)

@[expose] noncomputable def allNb (lp : Nat → Nat) (PL x : Nat) (f : Nat → Bool) : Bool :=
  allN (degK x) (fun k => f (nbK lp PL x k))

@[expose] noncomputable def adjK (lp : Nat → Nat) (x y : Nat) : Bool :=
  bAnd(Nat.blt y (nat_lit 4680), bAnd(Nat.blt x (nat_lit 4680),
    bIf(Nat.blt x (nat_lit 1755), bAnd(Nat.ble (nat_lit 1755) y, onLine lp x (Nat.sub y (nat_lit 1755))),
      bAnd(Nat.blt y (nat_lit 1755), onLine lp y (Nat.sub x (nat_lit 1755))))))

@[expose] noncomputable def incK (lp : Nat → Nat) (PL : Nat) : Bool :=
  bAnd(allN (nat_lit 1755) (fun x =>
      bAnd(allN (nat_lit 5) (fun k => strictB (plK PL x k) (fun v =>
          bAnd(Nat.blt v (nat_lit 2925), onLine lp x v))),
        allN (nat_lit 5) (fun k => allN k (fun j =>
          bIf(Nat.beq (plK PL x k) (plK PL x j), false, true))))),
    allN (nat_lit 2925) (fun v => allN (nat_lit 3) (fun k =>
      strictB (lp (Nat.add (Nat.mul (nat_lit 3) v) k)) (fun p =>
        anyN (nat_lit 5) (fun j => Nat.beq (plK PL p j) v)))))

@[expose] noncomputable def layAt (LAY x : Nat) : Nat := fw (nat_lit 4) LAY x

@[expose] noncomputable def layK (lp : Nat → Nat) (PL b cnt LAY PAR : Nat) : Bool :=
  bAnd(Nat.blt b (nat_lit 4680), bAnd(Nat.beq (layAt LAY b) (nat_lit 0),
  bAnd(Nat.beq (CFSG.KC.Loop.sumBelow (nat_lit 4680) (nat_lit 74)
      (fun x => nIf(Nat.beq (layAt LAY x) (nat_lit 8), nat_lit 1, nat_lit 0))) cnt,
  allN (nat_lit 4680) (fun x => strictB (layAt LAY x) (fun l =>
    strictB (fw (nat_lit 13) PAR x) (fun p =>
    bAnd(Nat.ble l (nat_lit 8),
    bAnd(bIf(Nat.beq x b, true, bAnd(adjK lp x p, Nat.beq (Nat.succ (layAt LAY p)) l)),
    bAnd(allNb lp PL x (fun y => Nat.ble (layAt LAY y) (Nat.succ l)),
      bIf(Nat.beq l (nat_lit 0), true, bIf(Nat.blt (nat_lit 7) l, true,
        allNb lp PL x (fun y => bIf(Nat.beq (Nat.succ (layAt LAY y)) l, Nat.beq y p, true)))))))))))))

@[expose] noncomputable def cycK (lp : Nat → Nat) (C : List Nat) : Bool :=
  bAnd(Nat.beq C.length (nat_lit 16), allN (nat_lit 16) (fun i =>
    bAnd(adjK lp (C.getD i 0) (C.getD (Nat.mod (Nat.add i (nat_lit 1)) (nat_lit 16)) 0),
      bIf(Nat.beq (C.getD i 0) (C.getD (Nat.mod (Nat.add i (nat_lit 2)) (nat_lit 16)) 0), false,
        true))))

@[expose] noncomputable def bindK (F FI A : Nat → Nat) (ws : List (List Nat)) : Bool :=
  allL (fun j w => strictB (A j) (fun a =>
    allN (nat_lit 1755) (fun x => Nat.beq (gp a x) (wPt F FI w x)))) ws 0

@[expose] noncomputable def lineMap (lp f : Nat → Nat) (v w : Nat) : Bool :=
  allN (nat_lit 3) (fun k => onLine lp (f (lp (Nat.add (Nat.mul (nat_lit 3) v) k))) w)

@[expose] noncomputable def actV (lp f : Nat → Nat) (y x : Nat) : Bool :=
  bIf(Nat.blt y (nat_lit 1755), bAnd(Nat.blt x (nat_lit 1755), Nat.beq (f y) x),
    bAnd(Nat.ble (nat_lit 1755) x, bAnd(Nat.blt x (nat_lit 4680),
      lineMap lp f (Nat.sub y (nat_lit 1755)) (Nat.sub x (nat_lit 1755)))))

@[expose] noncomputable def fixV (lp : Nat → Nat) (PL : Nat) (f : Nat → Nat) (a : Nat) : Bool :=
  bAnd(actV lp f a a, allNb lp PL a (fun y => actV lp f y y))

@[expose] noncomputable def recK (lp A : Nat → Nat) (k root cnt LAY ORD PR LB PS : Nat) : Bool :=
  bAnd(Nat.beq (fw (nat_lit 13) ORD 0) root,
  bAnd(allN cnt (fun i => strictB (fw (nat_lit 13) ORD i) (fun x => bAnd(Nat.blt x (nat_lit 4680),
    bIf(Nat.beq i (nat_lit 0), true, strictB (fw (nat_lit 11) PR i) (fun p =>
      strictB (fw (nat_lit 3) LB i) (fun j => bAnd(Nat.blt p i, bAnd(Nat.blt j k,
        actV lp (gp (A j)) (fw (nat_lit 13) ORD p) x)))))))),
    allN (nat_lit 4680) (fun x => bIf(Nat.beq (layAt LAY x) (nat_lit 8),
      strictB (fw (nat_lit 13) PS x) (fun q => bAnd(Nat.blt q cnt, Nat.beq (fw (nat_lit 13) ORD q) x)),
      true))))

@[expose] noncomputable def locK (lp F FI : Nat → Nat) (PL a b0 d : Nat) (ws : List (List Nat))
    (prs : List Nat) : Bool :=
  bAnd(Nat.beq ws.length (Nat.mul d (Nat.sub d 1)), bAnd(Nat.beq prs.length ws.length,
  bAnd(Nat.beq (ws.headD [1]).length 0, bAnd(Nat.beq (prs.headD 0) 1,
  bAnd(distK (fun i => prs.getD i 0) prs.length,
  bAnd(allN d (fun u => allN d (fun u' => bIf(Nat.beq u u', true,
    memK (Nat.add (Nat.mul u d) u') prs))),
    allL (fun i w => strictB (prs.getD i 0) (fun pr =>
      strictB (Nat.div pr d) (fun u => strictB (Nat.mod pr d) (fun u' =>
      bAnd(Nat.blt u d, bAnd(bIf(Nat.beq u u', false, true),
      bAnd(actV lp (wPt F FI w) a a, bAnd(actV lp (wPt F FI w) b0 b0,
      bAnd(actV lp (wPt F FI w) (nbK lp PL a 0) (nbK lp PL a u),
        actV lp (wPt F FI w) (nbK lp PL a 1) (nbK lp PL a u')))))))))) ws 0))))))

@[expose] noncomputable def tn1 (t n1 i x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (gp n1 x) (fun _ ih => gp t ih) i

@[expose] noncomputable def smallK (lp A : Nat → Nat) (PL n1 t q0 : Nat) : Bool :=
  bAnd(allN (nat_lit 1755) (fun x => Nat.beq (gp n1 (gp n1 x)) x),
  bAnd(Nat.beq (gp n1 0) 0, bAnd(Nat.beq (gp t 0) 0, bAnd(lineMap lp (gp t) 0 0,
  bAnd(lineMap lp (gp q0) 0 0,
  bAnd(allN (nat_lit 5) (fun k => strictB (plK PL 0 k) (fun v => bIf(Nat.beq v 0, true,
    anyN (nat_lit 4) (fun i => lineMap lp (tn1 t n1 i) 0 v)))),
  bAnd(allN (nat_lit 5) (fun j => strictB (A j) (fun a =>
    bAnd(Nat.beq (gp n1 (gp a (gp n1 0))) 0, lineMap lp (fun x => gp n1 (gp a (gp n1 x))) 0 0))),
    allN (nat_lit 1755) (fun p => bIf(Nat.beq p 0, true, bIf(Nat.beq (gp t p) p,
      anyN (nat_lit 5) (fun j => bIf(Nat.beq (gp (A j) p) p, false, true)), true))))))))))

@[expose] noncomputable def farK (LAY : Nat) : Bool :=
  bAnd(Nat.beq (layAt LAY 87) 8, allN (nat_lit 1755) (fun p => strictB (layAt LAY p) (fun l =>
    bIf(Nat.ble l 6, true, Nat.beq l 8))))

@[expose] noncomputable def sigR (A : Nat → Nat) (ORD PR LB k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => k)
    (fun _ ih j => nIf(Nat.beq j 0, k,
      strictN (ih (fw (nat_lit 11) PR j)) (fun y => gp (A (fw (nat_lit 3) LB j)) y)))

@[expose] noncomputable def sigK (A : Nat → Nat) (LAY ORD PR LB PS k x : Nat) : Nat :=
  nIf(Nat.ble (layAt LAY x) 6, x,
    strictN (fw (nat_lit 13) PS x) (fun j => sigR A ORD PR LB k (Nat.succ j) j))

@[expose] noncomputable def cycFrom (g : Nat → Nat) (x : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun y => Nat.beq y x)
    (fun _ ih y => bIf(Nat.beq y x, false, strictB (g y) ih))

@[expose] noncomputable def witRow (A : Nat → Nat) (LAY ORD PR LB PS n1 q0 i : Nat)
    (r : List Nat) : Bool :=
  strictB (fw (nat_lit 13) ORD i) (fun k => strictB (r.getD 1 0) (fun x =>
  bIf(Nat.beq (r.headD 0) 0, Nat.beq i 0,
  bAnd(bIf(Nat.beq i 0, false, true), bAnd(Nat.blt x (nat_lit 1755),
  bIf(Nat.beq (r.headD 0) 1,
    strictB (gp n1 (sigK A LAY ORD PR LB PS k x)) (fun y =>
      bIf(Nat.beq (gp n1 (sigK A LAY ORD PR LB PS k y)) x, false, true)),
    bAnd(Nat.beq (r.headD 0) 2, strictB (r.getD 2 0) (fun L =>
      bAnd(Nat.blt 0 L, bAnd(bIf(Nat.beq (Nat.mod (nat_lit 35942400) L) 0, false, true),
        cycFrom (fun y => gp n1 (sigK A LAY ORD PR LB PS k (gp q0 y))) x (Nat.sub L 1)
          (gp n1 (sigK A LAY ORD PR LB PS k (gp q0 x)))))))))))))

@[expose] noncomputable def witK (A : Nat → Nat) (LAY ORD PR LB PS n1 q0 i₀ : Nat)
    (R : List (List Nat)) : Bool :=
  allL (fun i r => witRow A LAY ORD PR LB PS n1 q0 (Nat.add i₀ i) r) R 0

end CFSG.KC.TitsOctK

end
