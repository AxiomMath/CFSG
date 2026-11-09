module

public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.FourJoinedK

public section

namespace CFSG.KC.FourJB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin

@[expose] noncomputable def imgStepK (nc : Nat) (I : Nat → Nat) (f : Nat → Nat) (s d : Nat) : Bool :=
  allN nc fun j => Nat.beq (I (Nat.add (Nat.mul d nc) j)) (f (I (Nat.add (Nat.mul s nc) j)))

@[expose] noncomputable def bfsBK (cs : List Nat) (nc kp ng N : Nat) (act : Nat → Nat → Nat)
    (PAR LAB POS I S : Nat → Nat) : Bool :=
  bAnd(Nat.beq nc cs.length, bAnd(Nat.blt kp nc,
  bAnd(allN nc (fun j => Nat.beq (I j) (cs.getD j (nat_lit 0))),
  bAnd(allN N (fun c => bIf(Nat.beq c (nat_lit 0), true,
      strictB (PAR c) fun p => strictB (LAB c) fun l =>
      bAnd(Nat.blt p c, bAnd(Nat.blt l ng, imgStepK nc I (act l) p c)))),
  bAnd(allN N (fun i => allN ng fun k => strictB (POS (Nat.add (Nat.mul i ng) k)) fun q =>
      bAnd(Nat.blt q N, imgStepK nc I (act k) i q)),
    distinctK N (fun i => I (Nat.add (Nat.mul i nc) kp)) S)))))

@[expose] noncomputable def chaseP (pm : Nat → Nat → Nat) (L : Nat → Nat) (len : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih o x => pm (L o) (ih (Nat.succ o) x)) len

@[expose] noncomputable def chasePT (pm : Nat → Nat → Nat) (O L : Nat → Nat) (t x : Nat) : Nat :=
  chaseP pm L (Nat.sub (O (Nat.succ t)) (O t)) (O t) x

@[expose] noncomputable def chaseR (w : Nat) (lf L : Nat → Nat) (len : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih o x => pg w (mask w) (lf (L o)) (ih (Nat.succ o) x)) len

@[expose] noncomputable def treeCh (act : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (fuel : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih a x => nIf(Nat.beq a (nat_lit 0), x, act (LAB a) (ih (PAR a) x))) fuel

@[expose] noncomputable def mtI (N : Nat) (MT : Nat → Nat) (a b : Nat) : Nat :=
  MT (Nat.add (Nat.mul a N) b)

@[expose] noncomputable def cmBK (N : Nat) (MT : Nat → Nat) (a b : Nat) : Bool :=
  Nat.beq (mtI N MT a b) (mtI N MT b a)

@[expose] noncomputable def mtBK(N ng : Nat) (PAR LAB POS MT : Nat → Nat) : Bool :=
  allN N fun a => allN N fun b => strictB (mtI N MT a b) fun c =>
    bAnd(Nat.blt c N, bIf(Nat.beq a (nat_lit 0), Nat.beq c b,
      Nat.beq c (POS (Nat.add (Nat.mul (mtI N MT (PAR a) b) ng) (LAB a)))))

@[expose] noncomputable def kleinMK (N m : Nat) (MT PX PY PXY : Nat → Nat) : Bool :=
  allN m fun i => strictB (PX i) fun x => strictB (PY i) fun y =>
    bAnd(Nat.blt x N, bAnd(Nat.blt y N, bAnd(Nat.blt (PXY i) N,
    bAnd(Nat.blt (nat_lit 0) x, bAnd(Nat.blt (nat_lit 0) y, bAnd(bIf(Nat.beq x y, false, true),
    bAnd(Nat.beq (mtI N MT x x) (nat_lit 0), bAnd(Nat.beq (mtI N MT y y) (nat_lit 0),
    bAnd(cmBK N MT x y, Nat.beq (mtI N MT x y) (PXY i))))))))))

@[expose] noncomputable def treeMK (N m nBig : Nat) (MT PX PY PAR : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) nBig, bAnd(Nat.ble nBig m, allN nBig fun i =>
    bIf(Nat.beq i (nat_lit 0), true, strictB (PAR i) fun p =>
      bAnd(Nat.blt p i, bAnd(cmBK N MT (PX i) (PX p), bAnd(cmBK N MT (PX i) (PY p),
        bAnd(cmBK N MT (PY i) (PX p), cmBK N MT (PY i) (PY p))))))))

@[expose] noncomputable def compMK (N m : Nat) (MT PX PY PXY : Nat → Nat) (INV : Nat)
    (FM : Nat → Nat) : Bool :=
  bAnd(allN N (fun u => bIf(CFSG.KC.FourJ.bitK INV u, true,
      bIf(Nat.beq (mtI N MT u u) (nat_lit 0), Nat.beq u (nat_lit 0), true))),
  bAnd(allN N (fun u => strictB (FM u) fun f => bAnd(Nat.blt f (Nat.shiftLeft 1 m),
      allN m fun i => bIf(CFSG.KC.FourJ.bitK f i,
        bIf(Nat.beq u (PX i), true, bIf(Nat.beq u (PY i), true, Nat.beq u (PXY i))), true))),
    allN N (fun u => bIf(CFSG.KC.FourJ.bitK INV u, strictB (FM u) fun f =>
      allN N fun v => bIf(CFSG.KC.FourJ.bitK INV v, bIf(Nat.beq u v, true,
        bIf(cmBK N MT u v, Nat.blt (nat_lit 0) (Nat.land f (FM v)), true)), true), true))))

@[expose] noncomputable def isoBK (cs : List Nat) (nc : Nat) (I : Nat → Nat) (ct cg : Nat → Nat → Nat)
    (m nBig : Nat) (PX PY IJ : Nat → Nat) : Bool :=
  allN (Nat.sub m nBig) fun t => strictB (Nat.add nBig t) fun i => strictB (IJ t) fun j =>
    bAnd(Nat.blt j nBig, allN nc fun c => strictB (cg t (cs.getD c (nat_lit 0))) fun gb =>
      bAnd(Nat.beq (cg t (I (Nat.add (Nat.mul (PX j) nc) c))) (ct (PX i) gb),
        Nat.beq (cg t (I (Nat.add (Nat.mul (PY j) nc) c))) (ct (PY i) gb)))

@[expose] noncomputable def selI (N : Nat) (MT : Nat → Nat) (x y c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), x, nIf(Nat.beq c (nat_lit 1), y, mtI N MT x y))

@[expose] noncomputable def normBK (cs : List Nat) (nc : Nat) (I : Nat → Nat)
    (ct cz czi : Nat → Nat → Nat) (N nBig nX : Nat) (MT PX PY NJ NCX NCY : Nat → Nat) : Bool :=
  allN nX fun k => strictB (NJ k) fun j => strictB (PX j) fun x => strictB (PY j) fun y =>
    bAnd(Nat.blt j nBig, allN nc fun c => strictB (cs.getD c (nat_lit 0)) fun b =>
      strictB (cz k b) fun zb =>
      bAnd(Nat.beq (cz k (czi k b)) b,
      bAnd(Nat.beq (cz k (I (Nat.add (Nat.mul x nc) c))) (ct (selI N MT x y (NCX k)) zb),
        Nat.beq (cz k (I (Nat.add (Nat.mul y nc) c))) (ct (selI N MT x y (NCY k)) zb))))

@[expose] noncomputable def pmX (nX : Nat) (pz pzi : Nat → Nat → Nat) (l x : Nat) : Nat :=
  nIf(Nat.blt l nX, pz l x, nIf(Nat.blt l (Nat.add nX nX), pzi (Nat.sub l nX) x, x))

@[expose] noncomputable def invBK (cs : List Nat) (nc : Nat) (pa pai pb pbi : Nat → Nat) : Bool :=
  allN nc fun c => strictB (cs.getD c (nat_lit 0)) fun b =>
    bAnd(Nat.beq (pa (pai b)) b, Nat.beq (pb (pbi b)) b)

@[expose] noncomputable def genBK (cs : List Nat) (nc : Nat) (pA pB : Nat → Nat)
    (cu : Nat → Nat → Nat) : Bool :=
  allN nc fun c => strictB (cs.getD c (nat_lit 0)) fun b =>
    bAnd(Nat.beq (pA b) (cu (nat_lit 0) b), Nat.beq (pB b) (cu (nat_lit 1) b))

@[expose] noncomputable def chaseT (w : Nat) (lf O L : Nat → Nat) (t x : Nat) : Nat :=
  chaseR w lf L (Nat.sub (O (Nat.succ t)) (O t)) (O t) x

end CFSG.KC.FourJB

end
