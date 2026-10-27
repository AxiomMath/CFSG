module

public import Certificates.Data.Kernel.EvenBN.Thm49EF6

public section

namespace CFSG.KD.T49

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def tg (w T i : Nat) : Nat := pg w (mask w) T i

@[expose] noncomputable def tsetK (w T i v : Nat) : Nat :=
  Nat.lor (Nat.xor T (Nat.land T (Nat.shiftLeft (mask w) (Nat.mul w i))))
    (Nat.shiftLeft v (Nat.mul w i))

@[expose] noncomputable def nthK (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def nthW (l : List (List Int)) (i : Nat) : List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Int) x (fun j _ => ih j) i) l i

@[expose] noncomputable def memK (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) l

@[expose] noncomputable def rowK (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun m ih => tsetK 7 ih m (f m)) 92

@[expose] noncomputable def lpt (S SI : Nat → Nat) (z : Int) (x : Nat) : Nat :=
  strictN (CFSG.KS.Mathieu.icode z) (fun c =>
    ap (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
      S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
      SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) x)

@[expose] noncomputable def wpt (S SI : Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun z _ ih x => lpt S SI z (ih x)) w x

@[expose] noncomputable def wipt (S SI : Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun z _ ih x => ih (lpt SI S z x)) w x

@[expose] noncomputable def pick3 (B0 B1 B2 b : Nat) : Nat :=
  nIf(Nat.beq b (nat_lit 0), B0, nIf(Nat.beq b (nat_lit 1), B1, B2))

@[expose] noncomputable def pick4 (v0 v1 v2 v3 j : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 0), v0, nIf(Nat.beq j (nat_lit 1), v1, nIf(Nat.beq j (nat_lit 2), v2, v3)))

@[expose] noncomputable def lamPt (U UI : Nat → Nat) (B0 B1 B2 b : Nat) (w : List Int) (x : Nat) :
    Nat :=
  wpt U UI w (ap (pick3 B0 B1 B2 b) (wipt U UI w x))

structure TOW where
  F : Nat → Nat
  FI : Nat → Nat
  D : Nat → Nat
  DI : Nat → Nat
  Z : Nat
  ew : List Int
  e1w : List Int
  e1iw : List Int
  yp : Nat
  r2 : Nat
  fz : List Nat
  lb : List Nat
  lw : List (List Int)
  s1 : Nat
  s2 : Nat
  igs : Nat
  steps : List Nat
  psteps : List Nat
  MT : Nat
  PT : Nat
  a : Nat
  b : Nat
  ABT : Nat
  tree : Nat
  T : Nat
  Y : Nat
  RK : Nat
  KA : List Nat
  b1 : Nat
  mc1 : Nat
  t0 : Nat
  t1 : Nat
  cl0 : List Nat
  cl1 : List Nat

@[expose] noncomputable def igK (W : TOW) (l : Nat) : Nat := tg 7 W.igs l

@[expose] noncomputable def mtK (W : TOW) (i m : Nat) : Nat := tg 7 W.MT (Nat.add (Nat.mul 92 i) m)

@[expose] noncomputable def ptK (W : TOW) (p q : Nat) : Nat := tg 7 W.PT (Nat.add (Nat.mul 92 p) q)

@[expose] noncomputable def abK (W : TOW) (p q : Nat) : Nat :=
  tg 10 W.ABT (Nat.add (Nat.mul 92 p) q)

@[expose] noncomputable def fy (r : Nat) : Nat := Nat.land r 127

@[expose] noncomputable def fx (r : Nat) : Nat := Nat.land (Nat.shiftRight r 7) 127

@[expose] noncomputable def fl (r : Nat) : Nat := Nat.shiftRight r 14

@[expose] noncomputable def mapFy (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun r _ ih => fy r :: ih) l

@[expose] noncomputable def covK (W : TOW) : List Nat :=
  igK W 0 :: igK W 1 :: igK W 2 :: igK W 3 :: igK W 4 :: mapFy W.steps

@[expose] noncomputable def fzIdx (fz : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun y _ ih i => tsetK 7 (ih (Nat.succ i)) y (Nat.succ i)) fz 0

structure MPerms where
  u1 : Nat
  u2 : Nat
  u1i : Nat
  u2i : Nat
  zp : Nat
  l1 : Nat

@[expose] noncomputable def MPerms.U (P : MPerms) (j : Nat) : Nat := nIf(Nat.beq j 0, P.u1, P.u2)

@[expose] noncomputable def MPerms.UI (P : MPerms) (j : Nat) : Nat := nIf(Nat.beq j 0, P.u1i, P.u2i)

@[expose] noncomputable def lamK (W : TOW) (P : MPerms) (i x : Nat) : Nat :=
  nIf(Nat.beq i 0, x, lamPt P.U P.UI W.Z P.zp P.l1 (nthK W.lb (Nat.sub i 1))
    (nthW W.lw (Nat.sub i 1)) x)

@[expose] noncomputable def keyM (W : TOW) (P : MPerms) (i : Nat) : Nat :=
  Nat.add (lamK W P i W.s1) (Nat.shiftLeft (lamK W P i W.s2) 11)

@[expose] noncomputable def keysK (W : TOW) (P : MPerms) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => tsetK 22 ih i (keyM W P i)) 92

@[expose] noncomputable def mactK (W : TOW) (P : MPerms) (FZ : Nat) (i m : Nat) : Nat :=
  nIf(Nat.beq i 0, m, nIf(Nat.beq m 0, 0, tg 7 FZ (lamK W P i (nthK W.fz (Nat.sub m 1)))))

@[expose] noncomputable def keyPQ (W : TOW) (P : MPerms) (p q : Nat) : Nat :=
  Nat.add (ap W.Z (lamK W P p (lamK W P q W.s1)))
    (Nat.shiftLeft (ap W.Z (lamK W P p (lamK W P q W.s2))) 11)

@[expose] noncomputable def ptOK (KS : Nat) (k v : Nat) : Bool :=
  bIf(Nat.blt v 92, Nat.beq (tg 22 KS v) k, allN 92 (fun w => bIf(Nat.beq (tg 22 KS w) k, false, true)))

@[expose] noncomputable def stepsOK (W : TOW) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih S => bAnd(Nat.blt (fl r) 5, bAnd(bitK S (fx r), bAnd(Nat.blt (fy r) 92,
      bAnd(Nat.beq (mtK W (igK W (fl r)) (fx r)) (fy r), ih (setK S (fy r)))))))

@[expose] noncomputable def rootMask (W : TOW) : Nat :=
  setK (setK (setK (setK (setK 0 (igK W 0)) (igK W 1)) (igK W 2)) (igK W 3)) (igK W 4)

@[expose] noncomputable def maskL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun y _ ih => setK ih y) l

@[expose] noncomputable def mpermsOK (W : TOW) (P : MPerms) : Bool :=
  bAnd(Nat.beq P.u1 (wd W.F W.FI Certificates.Thm49E.u1Word),
  bAnd(Nat.beq P.u2 (wd W.F W.FI Certificates.Thm49E.u2Word),
  bAnd(isPerm P.u1 P.u1i, bAnd(isPerm P.u2 P.u2i,
  bAnd(Nat.beq P.zp (wd W.F W.FI Certificates.Thm49E.zpWord),
  Nat.beq P.l1 (pmul (pmul (wd W.D W.DI W.e1w) W.Z) (wd W.D W.DI W.e1iw)))))))

@[expose] noncomputable def checkGen (W : TOW) (P : MPerms) : Bool :=
  bAnd(allN 4 (fun j => isPerm (W.F j) (W.FI j)),
  bAnd(allN 2 (fun j => isPerm (W.D j) (W.DI j)), bAnd(isPerm W.Z W.Z,
  bAnd(lettersK 4 Certificates.Thm49E.zpWord, bAnd(lettersK 4 Certificates.Thm49E.u1Word,
  bAnd(lettersK 4 Certificates.Thm49E.u2Word, bAnd(lettersK 4 Certificates.Thm49E.l2Word,
  bAnd(lettersK 4 Certificates.Thm49E.l3Word,
  bAnd(lettersK 2 W.ew, bAnd(lettersK 2 W.e1w, bAnd(lettersK 2 W.e1iw,
  bAnd(mpermsOK W P,
  bAnd(Nat.beq (pmul (wd W.D W.DI W.ew) W.Z) (pmul P.zp (wd W.D W.DI W.ew)),
  bAnd(Nat.beq (ap (wd W.D W.DI W.ew) 0) W.yp, bAnd(Nat.beq (ap (wd W.D W.DI W.e1w) 0) W.r2,
  bAnd(Nat.beq (pmul (wd W.D W.DI W.e1w) (wd W.D W.DI W.e1iw)) idP,
  bAnd(commP P.u1 W.Z, bAnd(commP P.u2 W.Z, bAnd(Nat.beq (ap P.u1 0) 0, bAnd(Nat.beq (ap P.u2 0) 0,
  bAnd(fixedK 1755 11 (mask 11) W.Z W.fz, bAnd(Nat.beq (lenK W.fz) 91,
  bAnd(Nat.beq (nthK W.fz 0) 0, bAnd(Nat.beq (lenK W.lb) 91, bAnd(Nat.beq (lenK W.lw) 91,
  bAnd(allK (fun w => lettersK 2 w) W.lw,
  allN 91 (fun i => strictB (nthK W.lb i) (fun b => bAnd(Nat.blt b 3,
    Nat.beq (wpt P.U P.UI (nthW W.lw i) (pick3 0 W.yp W.r2 b)) (nthK W.fz i))))))))))))))))))))))))))))))

@[expose] noncomputable def checkTab (W : TOW) (P : MPerms) : Bool :=
  strictB (keysK W P) (fun KS => strictB (fzIdx W.fz) (fun FZ =>
  bAnd(Nat.blt W.s1 1755, bAnd(Nat.blt W.s2 1755,
  bAnd(allN 92 (fun i => allN i (fun j => bIf(Nat.beq (tg 22 KS i) (tg 22 KS j), false, true))),
  bAnd(allN 92 (fun i => allN 92 (fun m => Nat.beq (mtK W i m) (mactK W P FZ i m))),
  bAnd(allN 92 (fun p => allN 92 (fun q => ptOK KS (keyPQ W P p q) (ptK W p q))),
  allN 92 (fun p => allN 92 (fun q =>
    Nat.beq (abK W p q) (tg 10 W.RK (lamK W P p (lamK W P q W.b1))))))))))))

@[expose] noncomputable def checkSteps (W : TOW) (P : MPerms) : Bool :=
  strictB (wd W.F W.FI Certificates.Thm49E.l2Word) (fun L2 =>
  strictB (wd W.F W.FI Certificates.Thm49E.l3Word) (fun L3 =>
  bAnd(Nat.beq (igK W 0) 0, bAnd(Nat.beq (igK W 1) 1, bAnd(Nat.blt (igK W 2) 92,
  bAnd(Nat.blt (igK W 3) 92, bAnd(Nat.blt (igK W 4) 92,
  bAnd(Nat.blt (nat_lit 0) (igK W 2), bAnd(Nat.beq (nthK W.fz (Nat.sub (igK W 2) 1)) W.yp,
  bAnd(allN 1755 (fun x => Nat.beq (lamK W P (igK W 3) x) (ap L2 x)),
  bAnd(allN 1755 (fun x => Nat.beq (lamK W P (igK W 4) x) (ap L3 x)),
  bAnd(allN 5 (fun l => allN l (fun l' => bIf(Nat.beq (igK W l) (igK W l'), false, true))),
  bAnd(stepsOK W W.steps (rootMask W),
  strictB (maskL (covK W)) (fun CM =>
  bAnd(allK (fun x => allN 5 (fun l => bitK CM (mtK W (igK W l) x))) (covK W),
  bAnd(allK (fun r => bAnd(Nat.blt (fy r) 92, bAnd(bitK CM (fx r), bAnd(bitK CM (fl r),
    allN 1755 (fun x => Nat.beq (lamK W P (fy r) x) (lamK W P (fx r) (lamK W P (fl r) x))))))) W.psteps,
  allN 92 (fun y => bIf(bitK CM y, true, memK y (mapFy W.psteps)))))))))))))))))))

@[expose] noncomputable def parK (W : TOW) (c : Nat) : Nat := Nat.land (tg 11 W.tree c) 511

@[expose] noncomputable def genK (W : TOW) (c : Nat) : Nat := Nat.shiftRight (tg 11 W.tree c) 9

@[expose] noncomputable def mulF (W : TOW) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun a _ => a)
    (fun _ ih a b => nIf(Nat.beq b 0, a,
      tg 9 W.T (Nat.add (Nat.mul 4 (ih a (parK W b))) (genK W b))))

@[expose] noncomputable def homF (W : TOW) (thr : Nat → Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih c => nIf(Nat.beq c 0, 0, mulF W 16 (ih (parK W c)) (thr (genK W c))))

@[expose] noncomputable def bitR (j : Nat) : Nat := nIf(Nat.beq j 3, 1, 0)

@[expose] noncomputable def bitF (W : TOW) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih c => nIf(Nat.beq c 0, 0, Nat.xor (ih (parK W c)) (bitR (genK W c))))

@[expose] noncomputable def kptF (W : TOW) (R : Nat → Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih c x => nIf(Nat.beq c 0, x, ih (parK W c) (R (genK W c) x)))

@[expose] noncomputable def reachF (W : TOW) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun c => Nat.beq c 0)
    (fun _ ih c => bIf(Nat.beq c 0, true, ih (parK W c)))

structure KPerms where
  h1 : Nat
  h2 : Nat
  la : Nat
  lbb : Nat
  y0 : Nat
  y0i : Nat
  zp : Nat

@[expose] noncomputable def KPerms.R (Q : KPerms) (j x : Nat) : Nat :=
  pick4 (ap Q.h1 x) (ap Q.h2 x) (ap Q.la (ap Q.lbb x)) x j

@[expose] noncomputable def keyF (W : TOW) (Q : KPerms) (c : Nat) : Nat :=
  Nat.add (Nat.mul (bitF W 16 c) 2048) (kptF W Q.R 16 c W.b1)

@[expose] noncomputable def rowH (W : TOW) (FZ : Nat) (h : Nat → Nat) : Nat :=
  rowK (fun m => nIf(Nat.beq m 0, 0, tg 7 FZ (h (nthK W.fz (Nat.sub m 1)))))

@[expose] noncomputable def rowR (W : TOW) (FZ : Nat) (Q : KPerms) (j : Nat) : Nat :=
  pick4 (rowH W FZ (ap Q.h1)) (rowH W FZ (ap Q.h2))
    (rowK (fun m => mtK W W.a (mtK W W.b m))) (rowK (fun m => m)) j

@[expose] noncomputable def kaOK (W : TOW) (FZ : Nat) (Q : KPerms) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih c => bAnd(bIf(Nat.beq c 0, Nat.beq r (rowK (fun m => m)),
      strictB (nthK W.KA (parK W c)) (fun A => strictB (rowR W FZ Q (genK W c)) (fun B =>
        Nat.beq r (rowK (fun m => tg 7 A (tg 7 B m)))))), ih (Nat.succ c)))

@[expose] noncomputable def kpermsOK (W : TOW) (P : MPerms) (Q : KPerms) : Bool :=
  bAnd(Nat.beq Q.h1 (wd W.F W.FI Certificates.Thm49E.h1Word),
  bAnd(Nat.beq Q.h2 (wd W.F W.FI Certificates.Thm49E.h2Word),
  bAnd(Nat.beq Q.y0 (wd W.F W.FI Certificates.Thm49E.y0Word),
  bAnd(isPerm Q.y0 Q.y0i, bAnd(Nat.beq Q.zp P.zp,
  bAnd(allN 1755 (fun x => Nat.beq (ap Q.la x) (lamK W P W.a x)),
  allN 1755 (fun x => Nat.beq (ap Q.lbb x) (lamK W P W.b x))))))))

@[expose] noncomputable def checkK (W : TOW) (P : MPerms) (Q : KPerms) : Bool :=
  strictB (fzIdx W.fz) (fun FZ =>
  bAnd(kpermsOK W P Q, bAnd(lettersK 4 Certificates.Thm49E.h1Word,
  bAnd(lettersK 4 Certificates.Thm49E.h2Word, bAnd(lettersK 4 Certificates.Thm49E.y0Word,
  bAnd(Nat.blt W.a 92, bAnd(Nat.blt W.b 92, bAnd(Nat.blt W.b1 1755,
  bAnd(commP Q.h1 W.Z, bAnd(commP Q.h1 Q.zp, bAnd(Nat.beq (ap Q.h1 0) 0,
  bAnd(commP Q.h2 W.Z, bAnd(commP Q.h2 Q.zp, bAnd(Nat.beq (ap Q.h2 0) 0,
  bAnd(commP (pmul Q.la Q.lbb) W.Z, bAnd(commP (pmul Q.la Q.lbb) Q.zp,
  bAnd(Nat.beq (parK W 1) 0, bAnd(Nat.beq (genK W 1) 0,
  bAnd(Nat.beq (parK W 2) 0, bAnd(Nat.beq (genK W 2) 1,
  bAnd(allN 512 (fun c => bIf(Nat.beq c 0, true,
    bAnd(Nat.blt (parK W c) c, bAnd(Nat.blt (genK W c) 4, reachF W 16 c)))),
  bAnd(allN 512 (fun c => Nat.beq (tg 10 W.RK (keyF W Q c)) (Nat.succ c)),
  bAnd(allN 512 (fun c => allN 4 (fun j => Nat.beq
    (tg 10 W.RK (Nat.add (Nat.mul (Nat.xor (bitF W 16 c) (bitR j)) 2048)
      (kptF W Q.R 16 c (Q.R j W.b1)))) (Nat.succ (tg 9 W.T (Nat.add (Nat.mul 4 c) j))))),
  bAnd(allN 512 (fun c => Nat.beq
    (tg 10 W.RK (Nat.add (Nat.mul (bitF W 16 c) 2048) (ap Q.y0 (kptF W Q.R 16 c (ap Q.y0i W.b1)))))
    (Nat.succ (tg 9 W.Y c))),
  bAnd(Nat.beq (tg 10 W.RK (Nat.add 2048 (ap W.Z W.b1))) (Nat.succ W.mc1),
  bAnd(Nat.beq (lenK W.KA) 512, bAnd(kaOK W FZ Q W.KA 0,
  bAnd(Nat.blt W.t0 512, bAnd(Nat.blt W.t1 512, bAnd(Nat.blt W.mc1 512,
  bAnd(allK (fun c => Nat.blt c 512) W.cl0, bAnd(allK (fun c => Nat.blt c 512) W.cl1,
  bAnd(allN 512 (fun d => List.rec (motive := fun _ => Bool) false
    (fun c _ ih => bIf(Nat.beq (mulF W 16 c d) (mulF W 16 d W.t0), true, ih)) W.cl0),
  allN 512 (fun d => List.rec (motive := fun _ => Bool) false
    (fun c _ ih => bIf(Nat.beq (mulF W 16 c d) (mulF W 16 d W.t1), true, ih)) W.cl1))))))))))))))))))))))))))))))))))

@[expose] noncomputable def iaK (W : TOW) (i3 i4 l : Nat) : Nat :=
  nIf(Nat.beq l 0, 1, nIf(Nat.beq l 1, 0, nIf(Nat.beq l 2, igK W 2, nIf(Nat.beq l 3, i3, i4))))

@[expose] noncomputable def p0K (W : TOW) (i3 i4 : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun l ih => tsetK 7 ih (igK W l) (iaK W i3 i4 l)) 5

@[expose] noncomputable def stage1F (W : TOW) (i3 i4 : Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun r _ ih p => ih (tsetK 7 p (fy r) (mtK W (iaK W i3 i4 (fl r)) (tg 7 p (fx r)))))

@[expose] noncomputable def stage2F (W : TOW) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun r _ ih p => ih (tsetK 7 p (fy r) (ptK W (tg 7 p (fx r)) (tg 7 p (fl r)))))

@[expose] noncomputable def actAt (W : TOW) (i3 i4 p x : Nat) : Bool :=
  allN 5 (fun l => Nat.beq (tg 7 p (mtK W (igK W l) x)) (mtK W (iaK W i3 i4 l) (tg 7 p x)))

@[expose] noncomputable def injK (p : Nat) : Bool :=
  allN 92 (fun x => bAnd(Nat.blt (tg 7 p x) 92,
    allN x (fun y => bIf(Nat.beq (tg 7 p x) (tg 7 p y), false, true))))

@[expose] noncomputable def qRowK (p K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x ih => tsetK 7 ih (tg 7 p x) (tg 7 p (tg 7 K x))) 92

@[expose] noncomputable def thrK (W : TOW) (c5 c6 sab : Nat) (j : Nat) : Nat :=
  tg 9 W.Y (pick4 c5 c6 sab W.mc1 j)

@[expose] noncomputable def th3K (W : TOW) (c5 c6 sab t : Nat) : Nat :=
  homF W (thrK W c5 c6 sab) 16 (homF W (thrK W c5 c6 sab) 16 (homF W (thrK W c5 c6 sab) 16 t))

@[expose] noncomputable def leafBadK (W : TOW) (c5 c6 sab : Nat) : Bool :=
  bIf(memK (th3K W c5 c6 sab W.t0) W.cl0, bIf(memK (th3K W c5 c6 sab W.t1) W.cl1, false, true), true)

@[expose] noncomputable def scan6 (W : TOW) (Q6 c5 sab : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih c => bAnd(bIf(Nat.beq r Q6, leafBadK W c5 c sab, true), ih (Nat.succ c)))

@[expose] noncomputable def scan5 (W : TOW) (Q5 Q6 sab : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih c => bAnd(bIf(Nat.beq r Q5, scan6 W Q6 c sab W.KA 0, true), ih (Nat.succ c)))

@[expose] noncomputable def pairK (W : TOW) (i3 i4 : Nat) : Bool :=
  strictB (stage1F W i3 i4 W.steps (p0K W i3 i4)) (fun p1 =>
  bIf(allK (fun x => actAt W i3 i4 p1 x) (covK W),
    strictB (stage2F W W.psteps p1) (fun p =>
    bIf(bAnd(allN 92 (fun x => actAt W i3 i4 p x), injK p),
      strictB (abK W (tg 7 p W.a) (tg 7 p W.b)) (fun ab1 =>
      bIf(Nat.beq ab1 0, true,
        strictB (qRowK p (nthK W.KA 1)) (fun Q5 => strictB (qRowK p (nthK W.KA 2)) (fun Q6 =>
          scan5 W Q5 Q6 (Nat.sub ab1 1) W.KA 0)))), true)), true))

@[expose] noncomputable def searchK (W : TOW) (i3 : Nat) : Bool := allN 92 (fun i4 => pairK W i3 i4)

structure TOOK (W : TOW) (P : MPerms) (Q : KPerms) : Prop where
  bindF : ∀ j < 4, CFSG.Sporadic.Schreier.Tits.titsGenArrs[j]! = unpack 1755 11 (W.F j)
  bindD : ∀ j < 2, CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[j]! = unpack 1755 11 (W.D j)
  bindZ : CFSG.Sporadic.Schreier.Tits.titsZArr = unpack 1755 11 W.Z
  gen : checkGen W P = true
  tab : checkTab W P = true
  steps : checkSteps W P = true
  codes : checkK W P Q = true
  search : ∀ i3 < 92, searchK W i3 = true

end CFSG.KD.T49

end
