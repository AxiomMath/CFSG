module

public import Certificates.Data.Kernel.SporSch.ClsAll

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11

@[expose] noncomputable def keyR (n w m BP : Nat) (f : Nat → Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t ih => Nat.add (Nat.mul ih n) (f (pg w m BP t)))

@[expose] noncomputable def keyK (n w m BP nb : Nat) (f : Nat → Nat) : Nat :=
  keyR n w m BP f nb

@[expose] noncomputable def elF (n w m nw nb : Nat) (LR TR : Nat → Nat) (j : Nat) : Nat → Nat :=
  apL w m (elemT n nw LR TR nb j)

@[expose] noncomputable def inR (lo hi u : Nat) : Bool := bAnd(Nat.ble lo u, Nat.blt u hi)

@[expose] noncomputable def xHdK (n w m nw : Nat) (GS GSI X XI : Nat → Nat)
    (XW : Nat → List Int) (nx : Nat) : Bool :=
  allN nx (fun t => bAnd(Nat.beq (X t) (wordK n w m (pidn n w) GS GSI (XW t)),
    permOK n w m nw (X t) (XI t)))

@[expose] noncomputable def clsXK (n w m nw nb nx : Nat) (LR TR E RP X : Nat → Nat)
    (UO CU JO CJ : Nat → Nat) (i : Nat) : Bool :=
  strictB (E (RP i)) (fun r =>
    bAnd(Nat.ble (UO i) (UO (Nat.succ i)), bAnd(Nat.ble (JO i) (JO (Nat.succ i)),
    bAnd(allN (Nat.sub (UO (Nat.succ i)) (UO i)) (fun u => strictB (CU (Nat.add (UO i) u))
      (fun t => bAnd(Nat.blt t nx, eqAllK n (fun x => pg w m (X t) (elF n w m nw nb LR TR r x))
        (fun x => elF n w m nw nb LR TR r (pg w m (X t) x))))),
    allN (Nat.sub (JO (Nat.succ i)) (JO i)) (fun u => strictB (CJ (Nat.add (JO i) u))
      (fun t => bAnd(Nat.blt t nx, eqAllK n (fun x => pg w m (X t) (elF n w m nw nb LR TR r x))
        (fun x => elF n w m nw nb LR TR r (pg w m (X t) x)))))))))

@[expose] noncomputable def rootHdK (n w m nw BP nb : Nat) (LR TR E O RP RO KL : Nat → Nat)
    (ncl R : Nat) : Bool :=
  bAnd(Nat.beq (RO (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (RO ncl) R,
  allN ncl (fun i => bAnd(Nat.ble (RO i) (RO (Nat.succ i)), bAnd(inR (O i) (O (Nat.succ i)) (RP i),
    Nat.beq (KL i) (keyK n w m BP nb (elF n w m nw nb LR TR (E (RP i)))))))))

@[expose] noncomputable def sqK (n w m nw BP nb : Nat) (LR TR RL RC RI KL : Nat → Nat)
    (ncl R j : Nat) : Bool :=
  strictB (keyK n w m BP nb (fun x => elF n w m nw nb LR TR j (elF n w m nw nb LR TR j x)))
    (fun k => strictB (RI j) (fun q => bIf(Nat.beq q (nat_lit 0),
      allN ncl (fun i => bIf(Nat.beq k (KL i), false, true)),
      strictB (Nat.sub q (nat_lit 1)) (fun p => bAnd(Nat.blt p R, bAnd(Nat.beq (RL p) j,
        Nat.beq k (KL (RC p))))))))

@[expose] noncomputable def rootK (N : Nat) (RL RC RI RO : Nat → Nat) (ncl p : Nat) : Bool :=
  strictB (RL p) (fun j => strictB (RC p) (fun i =>
    bAnd(Nat.blt j N, bAnd(Nat.beq (RI j) (Nat.succ p), bAnd(Nat.blt i ncl,
      inR (RO i) (RO (Nat.succ i)) p)))))

@[expose] noncomputable def siftP (n w m nw : Nat) (LR TRI : Nat → Nat) (BP : Nat) (f : Nat) :
    Nat → (Nat → Nat) → Option (Nat → Nat) :=
  Nat.rec (motive := fun _ => Nat → (Nat → Nat) → Option (Nat → Nat)) (fun _ g => some g)
    (fun _ ih l g =>
      (fun R => (fun k => Bool.rec (motive := fun _ => Option (Nat → Nat)) none
          (ih (Nat.succ l) (fun x => pg w m (TRI (Nat.add (roff n nw R) k)) (g x)))
          (Nat.blt k (rcnt R)))
        (rpos w m nw R (g (pg w m BP l))))
      (LR l))
    f

@[expose] noncomputable def cutK (n w m nw BP nb : Nat) (LR TR TRI RL RC UO CU X XI : Nat → Nat)
    (CT CP : Nat → Nat) (p : Nat) : Bool :=
  strictB (CT p) (fun c => bIf(Nat.beq c (nat_lit 0), true,
    strictB (RC p) (fun i => strictB (Nat.add (UO i) (Nat.sub c (nat_lit 1))) (fun u =>
    strictB (CU u) (fun t => strictB (CP p) (fun q =>
    bAnd(Nat.blt u (UO (Nat.succ i)), bAnd(Nat.blt q n,
    Option.rec (motive := fun _ => Bool) true (fun g => bIf(Nat.beq (g q) q, false, true))
      (siftP n w m nw LR TRI BP nb (nat_lit 0)
        (conjF w m (XI t) (X t) (elF n w m nw nb LR TR (RL p))))))))))))

@[expose] noncomputable def inQ (QJ : Nat → Nat) (m j : Nat) : Bool :=
  bIf(allN (nat_lit 8) (fun k => bIf(Nat.beq (QJ (Nat.add (Nat.mul (nat_lit 8) m) k)) j,
    false, true)), false, true)

@[expose] noncomputable def pairK (n w m nw BP nb : Nat) (LR TR RL RC RO CT QC QJ : Nat → Nat)
    (zc nq p : Nat) : Bool :=
  strictB (RC p) (fun i => bIf(bAnd(Nat.beq (CT p) (nat_lit 0), bIf(Nat.beq i zc, false, true)),
    strictB (RL p) (fun jx => strictB (RO i) (fun lo =>
    allN (Nat.sub (RO (Nat.succ i)) lo) (fun d => strictB (Nat.add lo d) (fun q =>
      bIf(Nat.beq (CT q) (nat_lit 0), strictB (RL q) (fun jy =>
        bIf(eqB w m BP nb (fun x => elF n w m nw nb LR TR jx (elF n w m nw nb LR TR jy
            (elF n w m nw nb LR TR jx x))) (elF n w m nw nb LR TR jy),
          bIf(allN nq (fun mm => bIf(bAnd(Nat.beq (QC mm) i, bAnd(inQ QJ mm jx, inQ QJ mm jy)),
            false, true)), false, true),
          true)), true))))),
    true))

@[expose] noncomputable def q8W (A B : Nat → Nat) (k x : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), x, nIf(Nat.beq k (nat_lit 1), A (A x),
  nIf(Nat.beq k (nat_lit 2), A x, nIf(Nat.beq k (nat_lit 3), A (A (A x)),
  nIf(Nat.beq k (nat_lit 4), B x, nIf(Nat.beq k (nat_lit 5), A (A (B x)),
  nIf(Nat.beq k (nat_lit 6), A (B x), A (A (A (B x))))))))))

@[expose] noncomputable def subK (n w m nw BP nb N ncl : Nat) (LR TR E RP JO CJ X XI : Nat → Nat)
    (QC QJ QW : Nat → Nat) (mm : Nat) : Bool :=
  strictB (QC mm) (fun i => strictB (Nat.mul (nat_lit 8) mm) (fun b8 =>
  bAnd(Nat.blt i ncl, bAnd(allN (nat_lit 8) (fun k => Nat.blt (QJ (Nat.add b8 k)) N),
  bAnd(Nat.beq (QJ (Nat.add b8 (nat_lit 1))) (E (RP i)),
  bAnd(allN (nat_lit 8) (fun k => eqB w m BP nb (elF n w m nw nb LR TR (QJ (Nat.add b8 k)))
    (q8W (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 2))))
      (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4)))) k)),
  bAnd(eqB w m BP nb (fun x => elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4)))
      (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4))) x))
    (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 1)))),
  bAnd(eqB w m BP nb (fun x => elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 2)))
      (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4)))
      (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 2))) x)))
    (elF n w m nw nb LR TR (QJ (Nat.add b8 (nat_lit 4)))),
  bAnd(Nat.ble (Nat.add (JO i) (nat_lit 5)) (JO (Nat.succ i)),
  allN (nat_lit 5) (fun a => allN (nat_lit 5) (fun b => bIf(Nat.blt a b,
    strictB (CJ (Nat.add (JO i) a)) (fun ta => strictB (CJ (Nat.add (JO i) b)) (fun tb =>
    strictB (QW (Nat.add (Nat.mul (nat_lit 25) mm) (Nat.add (Nat.mul (nat_lit 5) a) b)))
      (fun k => bAnd(Nat.blt k (nat_lit 8),
      allN (nat_lit 8) (fun k' => bIf(eqAllK n
        (fun x => pg w m (XI tb) (pg w m (X ta) (elF n w m nw nb LR TR (QJ (Nat.add b8 k))
          (pg w m (XI ta) (pg w m (X tb) x)))))
        (elF n w m nw nb LR TR (QJ (Nat.add b8 k'))), false, true)))))), true))))))))))))

end CFSG.KS.SporSch.MOC

end
