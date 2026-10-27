module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11

@[expose] noncomputable def apL (w m : Nat) (T : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun t _ ih x => strictN (ih x) (fun y => pg w m t y)) T x

@[expose] noncomputable def itF (f : Nat → Nat) (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => strictN y f) e

@[expose] noncomputable def fixB (w m BP nb : Nat) (f : Nat → Nat) : Bool :=
  allN nb (fun t => strictB (pg w m BP t) (fun b => Nat.beq (f b) b))

@[expose] noncomputable def ordF (w m BP nb : Nat) (f : Nat → Nat) (e : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) e, bAnd(fixB w m BP nb (itF f e),
    allN e (fun d => bIf(Nat.beq d (nat_lit 0), true, bIf(Nat.beq (Nat.mod e d) (nat_lit 0),
      bIf(fixB w m BP nb (itF f d), false, true), true)))))

@[expose] noncomputable def stepJ (w m BP nb mx my r s : Nat) (R : List Nat) (T : List Nat)
    (c : Nat) : Nat :=
  nIf(ordF w m BP nb (apL w m T) mx, Nat.succ c,
    nIf(ordF w m BP nb (apL w m T) my,
      Nat.add (Nat.add c (nat_lit 1048576))
        (nIf(bAnd(ordF w m BP nb (fun x => apL w m R (apL w m T x)) r,
            ordF w m BP nb (fun x => apL w m R (apL w m T (itF (apL w m R) (Nat.sub mx 1)
              (itF (apL w m T) (Nat.sub my 1) x)))) s),
          nat_lit 1099511627776, nat_lit 0)),
      c))

@[expose] noncomputable def enumJ (n w m nw BP nb mx my r s : Nat) (LR TR : Nat → Nat)
    (R : List Nat) : Nat → Nat → List Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → Nat → Nat)
    (fun _ L c => stepJ w m BP nb mx my r s R L.reverse c)
    (fun _ ih i L c => strictN (LR i) (fun Q =>
      foldUp (rcnt Q) (fun k c => strictN (TR (Nat.add (roff n nw Q) k)) (fun t =>
        ih (Nat.succ i) (List.cons t L) c)) c))

@[expose] noncomputable def cntJ (n w m nw BP nb mx my r s : Nat) (LR TR : Nat → Nat)
    (R : List Nat) (k₀ : Nat) : Nat :=
  strictN (LR (nat_lit 0)) (fun Q => strictN (TR (Nat.add (roff n nw Q) k₀)) (fun t =>
    enumJ n w m nw BP nb mx my r s LR TR R (Nat.sub nb (nat_lit 1)) (nat_lit 1) [t] (nat_lit 0)))

@[expose] noncomputable def cntJB (n w m nw BP nb mx my r s : Nat) (LR TR : Nat → Nat)
    (R : List Nat) (lo len : Nat) : Nat :=
  foldUp len (fun l c => strictN (Nat.add lo l) (fun k₀ =>
    nIf(Nat.blt k₀ (rcnt (LR (nat_lit 0))),
      Nat.add c (cntJ n w m nw BP nb mx my r s LR TR R k₀), c))) (nat_lit 0)

@[expose] noncomputable def elemTR (n nw : Nat) (LR TR : Nat → Nat) :
    Nat → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ acc => acc)
    (fun d ih j acc => (fun c =>
      ih (Nat.div j c) (List.cons (TR (Nat.add (roff n nw (LR d)) (Nat.mod j c))) acc))
      (rcnt (LR d)))

@[expose] noncomputable def elemT (n nw : Nat) (LR TR : Nat → Nat) (nb j : Nat) : List Nat :=
  elemTR n nw LR TR nb j []

@[expose] noncomputable def conjF (w m A Ai : Nat) (f : Nat → Nat) (x : Nat) : Nat :=
  pg w m A (f (pg w m Ai x))

@[expose] noncomputable def eqB (w m BP nb : Nat) (f g : Nat → Nat) : Bool :=
  allN nb (fun t => strictB (pg w m BP t) (fun b => Nat.beq (f b) (g b)))

@[expose] noncomputable def clsPtK (n w m nw BP nb N A Ai B Bi : Nat) (LR TR : Nat → Nat)
    (E IA IB PA LB DP : Nat → Nat) (c r0 k : Nat) : Bool :=
  bIf(Nat.blt k c, strictB (E k) (fun j =>
    bAnd(Nat.blt j N, bAnd(bIf(Nat.blt (Nat.succ k) c, Nat.blt j (E (Nat.succ k)), true),
    bAnd(Nat.blt (IA k) c, bAnd(Nat.blt (IB k) c,
    bAnd(eqB w m BP nb (conjF w m A Ai (apL w m (elemT n nw LR TR nb j)))
      (apL w m (elemT n nw LR TR nb (E (IA k)))),
    bAnd(eqB w m BP nb (conjF w m B Bi (apL w m (elemT n nw LR TR nb j)))
      (apL w m (elemT n nw LR TR nb (E (IB k)))),
    bIf(Nat.beq k r0, Nat.beq (DP k) (nat_lit 0),
      bAnd(Nat.blt (PA k) c, bAnd(Nat.blt (DP (PA k)) (DP k),
        bIf(Nat.beq (LB k) (nat_lit 0),
          eqB w m BP nb (apL w m (elemT n nw LR TR nb j))
            (conjF w m A Ai (apL w m (elemT n nw LR TR nb (E (PA k))))),
          eqB w m BP nb (apL w m (elemT n nw LR TR nb j))
            (conjF w m B Bi (apL w m (elemT n nw LR TR nb (E (PA k))))))
          )))))))))), true)

@[expose] noncomputable def clsPtHdK (n w m nw BP nb : Nat) (LR TR : Nat → Nat) (E : Nat → Nat)
    (c r0 R mx cap : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble c cap, bAnd(Nat.blt r0 c, bAnd(Nat.beq (E r0) R,
    ordF w m BP nb (apL w m (elemT n nw LR TR nb R)) mx))))

end CFSG.KS.SporSch.MOC

end
