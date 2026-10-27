module

public import Certificates.Data.Kernel.F3Bfs

public section

namespace CFSG.KS.Fi22LH

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ent (r x : Nat) : Nat := fld(r, Nat.mul (nat_lit 12) x, nat_lit 4095)

@[expose] noncomputable def e14 (r x : Nat) : Nat := fld(r, Nat.mul (nat_lit 14) x, nat_lit 16383)

@[expose] noncomputable def fd (q o m : Nat) : Nat := fld(q, o, m)

@[expose] noncomputable def memB (s y : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land s (Nat.shiftLeft (nat_lit 1) y))

@[expose] noncomputable def notB (b : Bool) : Bool := bIf(b, false, true)

@[expose] noncomputable def bEq (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def bsF (n : Nat) (f : Nat → Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun lo => nIf(Nat.blt lo n, Nat.shiftLeft (nat_lit 1) (f lo), nat_lit 0))
    (fun d ih lo => Nat.lor (ih lo) (ih (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))))

@[expose] noncomputable def bsP (n : Nat) (p : Nat → Bool) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun lo => nIf(Nat.blt lo n, nIf(p lo, Nat.shiftLeft (nat_lit 1) lo, nat_lit 0), nat_lit 0))
    (fun d ih lo => Nat.lor (ih lo) (ih (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))))

@[expose] noncomputable def bs (q : Nat) : Nat :=
  bsF (nat_lit 351) (fun j => ent q j) (nat_lit 9) (nat_lit 0)

@[expose] noncomputable def m3510 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3510)) (nat_lit 1)

@[expose] noncomputable def sb (q : Nat) : Nat := fld(q, nat_lit 4212, m3510)

@[expose] noncomputable def incK (q : Nat) : Bool :=
  bAnd(allN (nat_lit 350) (fun j => Nat.blt (ent q j) (ent q (Nat.succ j))),
    Nat.blt (ent q (nat_lit 350)) (nat_lit 3510))

@[expose] noncomputable def sum351 (f : Nat → Nat) : Nat :=
  CFSG.KC.Loop.sumBelow (nat_lit 351) (nat_lit 6) f

@[expose] noncomputable def rep (w v : Nat) : Nat :=
  Nat.mul v (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3584)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))

@[expose] noncomputable def masks : Nat :=
  Nat.lor (rep (nat_lit 2) (nat_lit 1)) (Nat.lor (Nat.shiftLeft (rep (nat_lit 4) (nat_lit 3)) (nat_lit 3584))
  (Nat.lor (Nat.shiftLeft (rep (nat_lit 8) (nat_lit 15)) (nat_lit 7168))
  (Nat.lor (Nat.shiftLeft (rep (nat_lit 16) (nat_lit 255)) (nat_lit 10752))
  (Nat.lor (Nat.shiftLeft (rep (nat_lit 32) (nat_lit 65535)) (nat_lit 14336))
  (Nat.lor (Nat.shiftLeft (rep (nat_lit 64) (nat_lit 4294967295)) (nat_lit 17920))
    (Nat.shiftLeft (rep (nat_lit 64) (nat_lit 1)) (nat_lit 21504)))))))

@[expose] noncomputable def mI (mk i : Nat) : Nat :=
  fld(mk, Nat.mul (nat_lit 3584) i, Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3584)) (nat_lit 1))

@[expose] noncomputable def popK (mk x : Nat) : Nat :=
  strictN (Nat.sub x (Nat.land (Nat.shiftRight x (nat_lit 1)) (mI mk (nat_lit 0)))) fun a =>
  strictN (Nat.add (Nat.land a (mI mk (nat_lit 1))) (Nat.land (Nat.shiftRight a (nat_lit 2)) (mI mk (nat_lit 1)))) fun b =>
  strictN (Nat.land (Nat.add b (Nat.shiftRight b (nat_lit 4))) (mI mk (nat_lit 2))) fun c =>
  strictN (Nat.land (Nat.add c (Nat.shiftRight c (nat_lit 8))) (mI mk (nat_lit 3))) fun d =>
  strictN (Nat.land (Nat.add d (Nat.shiftRight d (nat_lit 16))) (mI mk (nat_lit 4))) fun e =>
  strictN (Nat.land (Nat.add e (Nat.shiftRight e (nat_lit 32))) (mI mk (nat_lit 5))) fun f =>
    fld(Nat.mul f (mI mk (nat_lit 6)), nat_lit 3520, nat_lit 18446744073709551615)

@[expose] noncomputable def xiK (l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 4),
    nIf(Nat.blt l (nat_lit 2), nIf(Nat.beq l (nat_lit 0), nat_lit 3, nat_lit 5),
      nIf(Nat.beq l (nat_lit 2), nat_lit 29, nat_lit 44)),
    nIf(Nat.blt l (nat_lit 6), nIf(Nat.beq l (nat_lit 4), nat_lit 89, nat_lit 148), nat_lit 186))

@[expose] noncomputable def nbK (l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 3), nIf(Nat.beq l (nat_lit 0), nat_lit 641, nIf(Nat.beq l (nat_lit 1), nat_lit 911, nat_lit 738)),
    nIf(Nat.beq l (nat_lit 3), nat_lit 265, nIf(Nat.beq l (nat_lit 4), nat_lit 399, nat_lit 1042)))

@[expose] noncomputable def uiK (l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 3), nIf(Nat.beq l (nat_lit 0), nat_lit 889, nIf(Nat.beq l (nat_lit 1), nat_lit 2372, nat_lit 2865)),
    nIf(Nat.beq l (nat_lit 3), nat_lit 400, nIf(Nat.beq l (nat_lit 4), nat_lit 52, nat_lit 886)))

@[expose] noncomputable def hitT (par lab : Nat → Nat) (h l px n : Nat) : Nat :=
  nIf(Nat.beq n (nat_lit 0), nat_lit 0, nIf(Nat.blt px n, n,
    nIf(Nat.beq px n, nIf(Nat.beq (par n) h, nIf(Nat.beq (lab n) l, Nat.succ n, nat_lit 0), nat_lit 0),
      nat_lit 0)))

@[expose] noncomputable def bfsT (img : Nat → Nat → Nat) (nl : Nat) (pos par lab : Nat → Nat) (N : Nat) :
    Bool :=
  bAnd(Nat.beq (par (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (lab (nat_lit 0)) (nat_lit 0),
    Nat.beq (foldUp N (fun h n => nIf(Nat.blt h n,
      foldUp nl (fun l m => hitT par lab h l (pos (img h l)) m) n, nat_lit 0)) (nat_lit 1)) N))

@[expose] noncomputable def posK (pts pos : Nat → Nat) (none n N : Nat) : Bool :=
  bAnd(allN N (fun k => Nat.beq (pos (pts k)) k),
    allN n fun x => strictB (pos x) fun p =>
      bIf(Nat.beq p none, true, bAnd(Nat.blt p N, Nat.beq (pts p) x)))

@[expose] noncomputable def rowK (R : Nat → Nat) (al be bi op ol k : Nat) : Bool :=
  strictB (ent op k) fun p => bAnd(Nat.blt p k,
    strictB (R k) fun r => strictB (R p) fun rp =>
    strictB (nIf(Nat.beq (ent ol k) (nat_lit 1), al, be)) fun L =>
    strictB (nIf(Nat.beq (ent ol k) (nat_lit 1), al, bi)) fun Li =>
      allN (nat_lit 3510) fun x => Nat.beq (ent r x) (ent L (ent rp (ent Li x))))

@[expose] noncomputable def tallSl (R : Nat → Nat) (al be bi op ol s : Nat) : Bool :=
  allN (nat_lit 135) fun i => strictB (Nat.add (Nat.mul (nat_lit 135) s) i) fun k =>
    bIf(Nat.beq k (nat_lit 0), Nat.beq (R (nat_lit 0)) al, rowK R al be bi op ol k)

@[expose] noncomputable def fixSl (R Z : Nat → Nat) (s : Nat) : Bool :=
  allN (nat_lit 585) fun i => strictB (Nat.add (Nat.mul (nat_lit 585) s) i) fun k =>
    strictB (R k) fun r =>
      Nat.beq (Z k) (bsP (nat_lit 3510) (fun x => Nat.beq (ent r x) x) (nat_lit 12) (nat_lit 0))

@[expose] noncomputable def biK (be bi : Nat) : Bool :=
  allN (nat_lit 3510) fun x => bAnd(Nat.blt (ent bi x) (nat_lit 3510), Nat.beq (ent be (ent bi x)) x)

@[expose] noncomputable def setK (Q : Nat → Nat) (mk al be k : Nat) : Bool :=
  strictB (Q k) fun q => strictB (sb q) fun s =>
  bAnd(Nat.beq s (bs q), bAnd(Nat.beq (popK mk s) (nat_lit 351),
    strictB (fd q (nat_lit 7722) (nat_lit 16383)) fun pa =>
    strictB (fd q (nat_lit 7736) (nat_lit 16383)) fun pb =>
    bAnd(Nat.blt pa (nat_lit 14080), bAnd(Nat.blt pb (nat_lit 14080),
    bAnd(Nat.beq (bsF (nat_lit 351) (fun j => ent al (ent q j)) (nat_lit 9) (nat_lit 0)) (sb (Q pa)),
      Nat.beq (bsF (nat_lit 351) (fun j => ent be (ent q j)) (nat_lit 9) (nat_lit 0)) (sb (Q pb)))))))

@[expose] noncomputable def setSl (Q : Nat → Nat) (al be s : Nat) : Bool :=
  strictB masks fun mk => allN (nat_lit 704) fun i => setK Q mk al be (Nat.add (Nat.mul (nat_lit 704) s) i)

@[expose] noncomputable def orbBfsK (Q : Nat → Nat) : Bool :=
  CFSG.KC.F3Bfs.bfsOrderOK (fun k => fd (Q k) (nat_lit 7722) (nat_lit 16383))
    (fun k => fd (Q k) (nat_lit 7736) (nat_lit 16383)) (fun k => fd (Q k) (nat_lit 7750) (nat_lit 16383))
    (fun k => fd (Q k) (nat_lit 7764) (nat_lit 3)) (nat_lit 14080)

@[expose] noncomputable def walkStep (Q : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 14080), strictN (Q c) fun q =>
    strictN (fd q (nat_lit 7766) (nat_lit 16383)) fun n =>
      nIf(bAnd(Nat.blt n (nat_lit 14080), Nat.blt (sb q) (sb (Q n))), n, nat_lit 16383),
    nat_lit 16383)

@[expose] noncomputable def walkOK (Q : Nat → Nat) (lb m0 : Nat) : Bool :=
  bAnd(Nat.blt (foldN (nat_lit 14079) (fun _ c => walkStep Q c) m0) (nat_lit 14080),
    bAnd(Nat.beq (sb (Q (nat_lit 0))) (bs lb), bAnd(incK lb, Nat.beq (ent lb (nat_lit 0)) (nat_lit 0))))

@[expose] noncomputable def notInK (Q : Nat → Nat) (lb : Nat) : Bool :=
  strictB (bs lb) fun b => allN (nat_lit 14080) fun k => notB (Nat.beq (sb (Q k)) b)

@[expose] noncomputable def flatK (QA : Nat → Nat) (qa qb qbi : Nat) : Bool :=
  allN (nat_lit 14080) fun m => strictB (QA m) fun q =>
    bAnd(Nat.beq (e14 qa m) (fd q (nat_lit 7722) (nat_lit 16383)),
    bAnd(Nat.beq (e14 qb m) (fd q (nat_lit 7736) (nat_lit 16383)),
    bAnd(Nat.blt (e14 qbi m) (nat_lit 14080), Nat.beq (e14 qb (e14 qbi m)) m)))

@[expose] noncomputable def phiW (op ol qa qb qbi : Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 16383)
    (fun _ ih g m => nIf(Nat.beq g (nat_lit 0), e14 qa m,
      nIf(Nat.beq (ent ol g) (nat_lit 1), e14 qa (ih (ent op g) (e14 qa m)),
        e14 qb (ih (ent op g) (e14 qbi m))))) f

@[expose] noncomputable def phiK (op ol qa qb qbi : Nat) (ph : Nat → Nat) (l : Nat) : Bool :=
  strictB (ph l) fun t => strictB (xiK l) fun g =>
    allN (nat_lit 14080) fun m => Nat.beq (e14 t m) (phiW op ol qa qb qbi (nat_lit 12) g m)

@[expose] noncomputable def closedK (R : Nat → Nat) (lb b : Nat) : Bool :=
  allN (nat_lit 351) fun j => strictB (R (ent lb j)) fun r =>
    allN (nat_lit 351) fun t => memB b (ent r (ent lb t))

@[expose] noncomputable def rootK (R X : Nat → Nat) (lb b rq : Nat) : Bool :=
  bAnd(Nat.beq (fd (X (nat_lit 0)) (nat_lit 0) (nat_lit 4095)) (nat_lit 0),
  bAnd(Nat.beq (bsF (nat_lit 351) (fun k => fd (X k) (nat_lit 0) (nat_lit 4095)) (nat_lit 9) (nat_lit 0)) b,
  bAnd(posK (fun k => fd (X k) (nat_lit 0) (nat_lit 4095)) (fun x => ent rq x) (nat_lit 4095) (nat_lit 3510) (nat_lit 351),
    bfsT (fun h l => ent (R (ent lb l)) (fd (X h) (nat_lit 0) (nat_lit 4095))) (nat_lit 351)
      (fun x => ent rq x) (fun k => fd (X k) (nat_lit 12) (nat_lit 511))
      (fun k => fd (X k) (nat_lit 21) (nat_lit 511)) (nat_lit 351))))

@[expose] noncomputable def commHit (X : Nat → Nat) (lb cq r h j n : Nat) : Nat :=
  nIf(Nat.beq n (nat_lit 0), nat_lit 0, strictN (ent lb j) fun y =>
    nIf(Nat.beq (ent r y) y, strictN (fld(cq, Nat.mul (nat_lit 9) j, nat_lit 511)) fun p =>
      nIf(Nat.blt p n, n, nIf(Nat.beq p n, strictN (X n) fun x =>
        nIf(bAnd(Nat.beq (fd x (nat_lit 30) (nat_lit 4095)) y, Nat.beq (fd x (nat_lit 42) (nat_lit 511)) h),
          Nat.succ n, nat_lit 0), nat_lit 0)), n))

@[expose] noncomputable def commK (R X : Nat → Nat) (lb cq : Nat) : Bool :=
  bAnd(Nat.beq (fd (X (nat_lit 0)) (nat_lit 30) (nat_lit 4095)) (nat_lit 0),
  bAnd(Nat.beq (fd (X (nat_lit 0)) (nat_lit 42) (nat_lit 511)) (nat_lit 0),
  bAnd(allN (nat_lit 351) (fun j => strictB (fld(cq, Nat.mul (nat_lit 9) j, nat_lit 511)) fun p =>
      bAnd(Nat.blt p (nat_lit 351), Nat.beq (fd (X p) (nat_lit 30) (nat_lit 4095)) (ent lb j))),
    Nat.beq (foldUp (nat_lit 351) (fun h n => nIf(Nat.blt h n,
      strictN (R (fd (X h) (nat_lit 30) (nat_lit 4095))) fun r =>
        foldUp (nat_lit 351) (fun j m => commHit X lb cq r h j m) n, nat_lit 0)) (nat_lit 1)) (nat_lit 351))))

@[expose] noncomputable def rowF (R P QA : Nat → Nat) (lb0 b0 f : Nat) : Bool :=
  strictB (fd (P f) (nat_lit 0) (nat_lit 16383)) fun m =>
  bIf(memB b0 f, Nat.beq m (nat_lit 14080), strictB (R f) fun r =>
    bAnd(Nat.blt m (nat_lit 14080), bAnd(notB (Nat.beq m (nat_lit 0)), strictB (QA m) fun q =>
    bAnd(Nat.beq (fd q (nat_lit 7780) (nat_lit 4095)) f, strictB (sb q) fun s =>
      Nat.beq (sum351 fun j => strictN (ent lb0 j) fun x => strictN (ent r x) fun v =>
        nIf(memB s v, nIf(Nat.beq v x, nat_lit 1, nat_lit 0), nat_lit 1000)) (nat_lit 63)))))

@[expose] noncomputable def rowSl (R P QA : Nat → Nat) (lb0 b0 s : Nat) : Bool :=
  allN (nat_lit 440) fun i => strictB (Nat.add (Nat.mul (nat_lit 440) s) i) fun f =>
    bIf(Nat.blt f (nat_lit 3510), rowF R P QA lb0 b0 f, true)

@[expose] noncomputable def rowInvK (P QA : Nat → Nat) (b0 : Nat) : Bool :=
  allN (nat_lit 14080) fun m => strictB (fd (QA m) (nat_lit 7780) (nat_lit 4095)) fun i =>
    bIf(Nat.beq i (nat_lit 3510), true, bAnd(Nat.blt i (nat_lit 3510),
      bAnd(notB (memB b0 i), Nat.beq (fd (P i) (nat_lit 0) (nat_lit 16383)) m)))

@[expose] noncomputable def domK (R : Nat → Nat) (lb1 b1 f : Nat) : Bool :=
  bIf(memB b1 f, true, strictB (R f) fun r =>
    strictB (sum351 fun j => strictN (ent lb1 j) fun x => nIf(Nat.beq (ent r x) x, nat_lit 1, nat_lit 0))
      fun c => bAnd(Nat.blt (nat_lit 0) c, Nat.blt c (nat_lit 351)))

@[expose] noncomputable def domSl (R : Nat → Nat) (lb1 b1 s : Nat) : Bool :=
  allN (nat_lit 880) fun i => strictB (Nat.add (Nat.mul (nat_lit 880) s) i) fun f =>
    bIf(Nat.blt f (nat_lit 3510), domK R lb1 b1 f, true)

@[expose] noncomputable def fm (x y : Nat) : Nat :=
  fld(nat_lit 0x9c78e400, Nat.mul (nat_lit 2) (Nat.add (Nat.mul (nat_lit 4) x) y), nat_lit 3)

@[expose] noncomputable def co (c i : Nat) : Nat := fld(c, Nat.mul (nat_lit 2) i, nat_lit 3)

@[expose] noncomputable def hm (c d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.xor ih (fm (co c i) (fm (co d i) (co d i)))) (nat_lit 6)

@[expose] noncomputable def ld (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => nIf(Nat.beq (co c (Nat.sub (nat_lit 5) i)) (nat_lit 0), ih, co c (Nat.sub (nat_lit 5) i)))
    (nat_lit 6)

@[expose] noncomputable def sc (a c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.add ih (Nat.shiftLeft (fm a (co c i)) (Nat.mul (nat_lit 2) i))) (nat_lit 6)

@[expose] noncomputable def nm (c : Nat) : Nat := strictN (ld c) fun a => sc (fm a a) c

@[expose] noncomputable def wt (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => nIf(Nat.beq (co c i) (nat_lit 0), ih, Nat.succ ih)) (nat_lit 6)

@[expose] noncomputable def pr (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun i ih => fm ih (co c i)) (nat_lit 6)

@[expose] noncomputable def hy (j c : Nat) : Bool :=
  strictB (wt c) fun w => bIf(Nat.beq w (nat_lit 2), true,
    bAnd(Nat.beq w (nat_lit 6), Nat.beq (pr c) (Nat.succ j)))

@[expose] noncomputable def upK (up : Nat) : Bool :=
  bAnd(allN (nat_lit 692) (fun i => Nat.blt (ent up i) (ent up (Nat.succ i))),
    strictB (bsF (nat_lit 693) (fun i => ent up i) (nat_lit 10) (nat_lit 0)) fun s =>
      allN (nat_lit 4096) fun c => bEq (memB s c)
        (bAnd(notB (Nat.beq c (nat_lit 0)), bAnd(Nat.beq (hm c c) (nat_lit 0), Nat.beq (nm c) c))))

@[expose] noncomputable def starK (mk al eb b0 b1 h0 h1 h2 up pd : Nat) : Bool :=
  bAnd(Nat.beq (popK mk eb) (nat_lit 693),
    allN (nat_lit 3510) fun x =>
      bAnd(bEq (memB eb x) (bAnd(notB (Nat.beq x (nat_lit 0)), Nat.beq (ent al x) x)),
      bIf(memB eb x,
        strictB (ent up (fld(pd, Nat.mul (nat_lit 10) (popK mk (Nat.land eb (Nat.sub (Nat.shiftLeft (nat_lit 1) x) (nat_lit 1)))), nat_lit 1023))) fun c =>
          bAnd(bEq (memB h0 x) (hy (nat_lit 0) c), bAnd(bEq (memB h1 x) (hy (nat_lit 1) c),
          bAnd(bEq (memB h2 x) (hy (nat_lit 2) c),
          bAnd(bEq (memB b0 x) (memB h0 x), bEq (memB b1 x) (memB h2 x))))),
        bAnd(notB (memB h0 x), bAnd(notB (memB h1 x), notB (memB h2 x))))))

@[expose] noncomputable def failK (R : Nat → Nat) (al eb h1 : Nat) : Bool :=
  strictB (R (nat_lit 63)) fun t => strictB (R (nat_lit 2751)) fun c =>
  bAnd(memB eb (nat_lit 63), bAnd(memB h1 (nat_lit 63),
  bAnd(Nat.beq (ent t (nat_lit 2751)) (nat_lit 2751), bAnd(notB (Nat.beq (ent al (nat_lit 2751)) (nat_lit 2751)),
    allN (nat_lit 3510) fun x =>
      (fun ct => bEq (bAnd(memB h1 x, ct))
        (bAnd(ct, bAnd(Nat.beq (ent al x) x, bAnd(notB (Nat.beq x (nat_lit 0)),
          bAnd(Nat.beq (ent c x) x, notB (Nat.beq x (nat_lit 2751))))))))
        (bAnd(Nat.beq (ent t x) x, notB (Nat.beq x (nat_lit 63))))))))

@[expose] noncomputable def swapK (R C QA QB : Nat → Nat) (u lb0 lb1 u0 u1 : Nat) : Bool :=
  bAnd(Nat.beq (fd (C (nat_lit 0)) (nat_lit 0) (nat_lit 4095)) (nbK (nat_lit 0)),
  bAnd(posK (fun k => fd (C k) (nat_lit 0) (nat_lit 4095)) (fun x => fd (C x) (nat_lit 27) (nat_lit 4095))
      (nat_lit 4095) (nat_lit 3510) (nat_lit 3510),
  bAnd(bfsT (fun h l => ent (R (nbK l)) (fd (C h) (nat_lit 0) (nat_lit 4095))) (nat_lit 6)
      (fun x => fd (C x) (nat_lit 27) (nat_lit 4095)) (fun k => fd (C k) (nat_lit 12) (nat_lit 4095))
      (fun k => fd (C k) (nat_lit 24) (nat_lit 7)) (nat_lit 3510),
  bAnd(Nat.beq (ent u (fd (C (nat_lit 0)) (nat_lit 0) (nat_lit 4095))) (uiK (nat_lit 0)),
  bAnd(allN (nat_lit 3510) (fun k => bIf(Nat.beq k (nat_lit 0), true, strictB (C k) fun c =>
      Nat.beq (ent u (fd c (nat_lit 0) (nat_lit 4095)))
        (ent (R (uiK (fd c (nat_lit 24) (nat_lit 7)))) (ent u (fd (C (fd c (nat_lit 12) (nat_lit 4095))) (nat_lit 0) (nat_lit 4095)))))),
  bAnd(allN (nat_lit 3510) (fun x => bAnd(Nat.blt (ent u x) (nat_lit 3510), Nat.beq (ent u (ent u x)) x)),
  bAnd(Nat.blt u0 (nat_lit 14080), bAnd(Nat.blt u1 (nat_lit 14080),
  bAnd(strictB (sb (QB u0)) (fun s => allN (nat_lit 351) fun j => memB s (ent u (ent lb0 j))),
    strictB (sb (QA u1)) (fun s => allN (nat_lit 351) fun j => memB s (ent u (ent lb1 j))))))))))))

@[expose] noncomputable def farB (QA : Nat → Nat) (m : Nat) : Bool :=
  bAnd(notB (Nat.beq m (nat_lit 0)), Nat.beq (fd (QA m) (nat_lit 7780) (nat_lit 4095)) (nat_lit 3510))

@[expose] noncomputable def farK (QA TF ph : Nat → Nat) (b0 v0 nf : Nat) : Bool :=
  bAnd(Nat.blt v0 (nat_lit 14080), bAnd(farB QA v0, bAnd(allN v0 (fun m => notB (farB QA m)),
  bAnd(allN (nat_lit 7) (fun l => memB b0 (xiK l)),
  bAnd(Nat.beq (fd (TF (nat_lit 0)) (nat_lit 0) (nat_lit 16383)) v0,
  bAnd(posK (fun k => fd (TF k) (nat_lit 0) (nat_lit 16383)) (fun m => fd (QA m) (nat_lit 7792) (nat_lit 16383))
      (nat_lit 16383) (nat_lit 14080) nf,
  bAnd(bfsT (fun h l => e14 (ph l) (fd (TF h) (nat_lit 0) (nat_lit 16383))) (nat_lit 7)
      (fun m => fd (QA m) (nat_lit 7792) (nat_lit 16383)) (fun k => fd (TF k) (nat_lit 14) (nat_lit 16383))
      (fun k => fd (TF k) (nat_lit 28) (nat_lit 7)) nf,
    allN (nat_lit 14080) fun m => bIf(farB QA m,
      Nat.blt (fd (QA m) (nat_lit 7792) (nat_lit 16383)) nf, true))))))))

@[expose] noncomputable def minWitK (Z : Nat → Nat) (q bA bB k : Nat) : Bool :=
  strictB (foldN (nat_lit 351) (fun j c => strictN (ent q j) fun a =>
      nIf(memB bB a, Nat.land c (Z a), c)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3510)) (nat_lit 1))) fun c =>
    bAnd(Nat.blt k (nat_lit 3510), bAnd(memB c k, bAnd(notB (memB bA k),
      strictB (Nat.land c (Nat.sub (Nat.shiftLeft (nat_lit 1) k) (nat_lit 1))) fun y =>
        Nat.beq (Nat.sub y (Nat.land y bA)) (nat_lit 0))))

@[expose] noncomputable def edgeK (R Z : Nat → Nat) (q bA bB w : Nat) : Bool :=
  bAnd(minWitK Z q bA bB w, strictB (R w) fun r => allN (nat_lit 351) fun j => memB bB (ent r (ent q j)))

@[expose] noncomputable def muK (R Z P QA : Nat → Nat) (mk b0 bv f : Nat) : Bool :=
  strictB (P f) fun p => strictB (fd p (nat_lit 14) (nat_lit 4095)) fun w =>
  bIf(memB b0 f, Nat.beq w (nat_lit 3510),
    strictB (QA (fd p (nat_lit 0) (nat_lit 16383))) fun q => strictB (sb q) fun s =>
    bIf(Nat.beq (popK mk (Nat.land s bv)) (nat_lit 63), edgeK R Z q s bv w, Nat.beq w (nat_lit 3510)))

@[expose] noncomputable def muSl (R Z P QA : Nat → Nat) (mk b0 bv s : Nat) : Bool :=
  allN (nat_lit 880) fun i => strictB (Nat.add (Nat.mul (nat_lit 880) s) i) fun f =>
    bIf(Nat.blt f (nat_lit 3510), muK R Z P QA mk b0 bv f, true)

@[expose] noncomputable def rowSet (P QA : Nat → Nat) (f : Nat) : Nat := QA (fd (P f) (nat_lit 0) (nat_lit 16383))

@[expose] noncomputable def muHit (R Z M G : Nat → Nat) (mk mq q a h f n : Nat) : Nat :=
  nIf(Nat.beq n (nat_lit 0), nat_lit 0,
    strictN (fld(mq, Nat.mul (nat_lit 10) f, nat_lit 1023)) fun p =>
    nIf(Nat.beq p (nat_lit 1023), n,
    nIf(Nat.blt p n, n, strictN (G p) fun g =>
      nIf(Nat.beq (popK mk (Nat.land a g)) (nat_lit 63),
        nIf(Nat.beq p n, strictN (M n) fun t =>
          nIf(bAnd(Nat.beq (fd t (nat_lit 0) (nat_lit 4095)) f, bAnd(Nat.beq (fd t (nat_lit 12) (nat_lit 1023)) h,
              edgeK R Z q a g (fd t (nat_lit 22) (nat_lit 4095)))), Nat.succ n, nat_lit 0), nat_lit 0),
        n))))

@[expose] noncomputable def muTreeK (R Z P QA M G : Nat → Nat) (mk mq nm : Nat) : Bool :=
  strictB (fd (M (nat_lit 0)) (nat_lit 0) (nat_lit 4095)) fun f0 =>
  bAnd(Nat.beq (Nat.shiftRight (M (nat_lit 0)) (nat_lit 12)) (nat_lit 0), bAnd(Nat.blt f0 (nat_lit 3510), bAnd(Nat.blt (fd (P f0) (nat_lit 14) (nat_lit 4095)) (nat_lit 3510),
  bAnd(allN f0 (fun f => notB (Nat.blt (fd (P f) (nat_lit 14) (nat_lit 4095)) (nat_lit 3510))),
  bAnd(allN nm (fun k => strictB (fd (M k) (nat_lit 0) (nat_lit 4095)) fun f =>
      bAnd(Nat.blt (fd (P f) (nat_lit 14) (nat_lit 4095)) (nat_lit 3510),
        Nat.beq (G k) (sb (rowSet P QA f)))),
  bAnd(posK (fun k => fd (M k) (nat_lit 0) (nat_lit 4095)) (fun f => fld(mq, Nat.mul (nat_lit 10) f, nat_lit 1023))
      (nat_lit 1023) (nat_lit 3510) nm,
  bAnd(allN (nat_lit 3510) (fun f => bIf(Nat.blt (fd (P f) (nat_lit 14) (nat_lit 4095)) (nat_lit 3510),
      Nat.blt (fld(mq, Nat.mul (nat_lit 10) f, nat_lit 1023)) nm, true)),
    Nat.beq (foldUp nm (fun h n => nIf(Nat.blt h n,
      strictN (rowSet P QA (fd (M h) (nat_lit 0) (nat_lit 4095))) fun q => strictN (G h) fun a =>
        foldUp (nat_lit 3510) (fun f m => muHit R Z M G mk mq q a h f m) n, nat_lit 0)) (nat_lit 1)) nm)))))))

@[expose] noncomputable def edK (R Z P QA G : Nat → Nat) (mk mq ml qv bv h : Nat) : Bool :=
  strictB (P h) fun p => strictB (fd p (nat_lit 26) (nat_lit 16383)) fun e =>
  strictB (fd p (nat_lit 40) (nat_lit 4095)) fun g => strictB (fd p (nat_lit 52) (nat_lit 4095)) fun k =>
  bIf(memB bv h, bAnd(Nat.beq e (nat_lit 14080), bAnd(Nat.beq g (nat_lit 3510), Nat.beq k (nat_lit 3510))),
    bAnd(Nat.blt e (nat_lit 14080), strictB (sb (QA e)) fun s =>
    bAnd(strictB (R h) (fun r => allN (nat_lit 351) fun j => memB s (ent r (ent qv j))),
    bIf(farB QA e,
      strictB (fd p (nat_lit 64) (nat_lit 1023)) fun i =>
      bAnd(Nat.blt i (nat_lit 648), bAnd(Nat.beq (ent ml i) g,
      bAnd(allN i (fun t => notB (Nat.beq (popK mk (Nat.land s
          (G (fld(mq, Nat.mul (nat_lit 10) (ent ml t), nat_lit 1023))))) (nat_lit 63))),
        strictB (rowSet P QA g) fun q => strictB (G (fld(mq, Nat.mul (nat_lit 10) g, nat_lit 1023))) fun a =>
          bAnd(Nat.beq (popK mk (Nat.land s a)) (nat_lit 63), edgeK R Z q a s k)))),
      bAnd(Nat.beq g (nat_lit 3510), Nat.beq k (nat_lit 3510))))))

@[expose] noncomputable def edSl (R Z P QA G : Nat → Nat) (mk mq ml qv bv s : Nat) : Bool :=
  allN (nat_lit 440) fun i => strictB (Nat.add (Nat.mul (nat_lit 440) s) i) fun h =>
    bIf(Nat.blt h (nat_lit 3510), edK R Z P QA G mk mq ml qv bv h, true)

@[expose] noncomputable def mlK (mq ml nm : Nat) : Bool :=
  bAnd(Nat.beq nm (nat_lit 648), bAnd(allN (nat_lit 647) (fun i => Nat.blt (ent ml i) (ent ml (Nat.succ i))),
  bAnd(Nat.blt (ent ml (nat_lit 647)) (nat_lit 3510),
    allN (nat_lit 648) fun i => Nat.blt (fld(mq, Nat.mul (nat_lit 10) (ent ml i), nat_lit 1023)) nm)))

@[expose] noncomputable def rowSlW (R P QA : Nat → Nat) (lb0 s : Nat) : Bool :=
  strictB (bs lb0) fun b0 => rowSl R P QA lb0 b0 s

@[expose] noncomputable def domSlW (R : Nat → Nat) (lb1 s : Nat) : Bool :=
  strictB (bs lb1) fun b1 => domSl R lb1 b1 s

@[expose] noncomputable def rootW (R X : Nat → Nat) (lb rq : Nat) : Bool :=
  strictB (bs lb) fun b => bAnd(closedK R lb b, rootK R X lb b rq)

@[expose] noncomputable def starW (al eb lb0 lb1 h0 h1 h2 up pd : Nat) : Bool :=
  strictB masks fun mk => strictB (bs lb0) fun b0 => strictB (bs lb1) fun b1 =>
    starK mk al eb b0 b1 h0 h1 h2 up pd

@[expose] noncomputable def farW (QA TF ph : Nat → Nat) (lb0 v0 nf : Nat) : Bool :=
  strictB (bs lb0) fun b0 => farK QA TF ph b0 v0 nf

@[expose] noncomputable def muSlW (R Z P QA : Nat → Nat) (lb0 v0 s : Nat) : Bool :=
  strictB masks fun mk => strictB (bs lb0) fun b0 => strictB (sb (QA v0)) fun bv =>
    muSl R Z P QA mk b0 bv s

@[expose] noncomputable def muTreeW (R Z P QA M G : Nat → Nat) (mq nm : Nat) : Bool :=
  strictB masks fun mk => muTreeK R Z P QA M G mk mq nm

@[expose] noncomputable def edSlW (R Z P QA G : Nat → Nat) (mq ml v0 s : Nat) : Bool :=
  strictB masks fun mk => strictB (QA v0) fun qv => strictB (sb qv) fun bv =>
    edSl R Z P QA G mk mq ml qv bv s

end CFSG.KS.Fi22LH

end
