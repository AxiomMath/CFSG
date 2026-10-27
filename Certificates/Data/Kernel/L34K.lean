module

public import Certificates.Data.Kernel.BfsPinSlice
public import Certificates.Data.Kernel.HeAutK

public section

namespace CFSG.KC.L34K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KLie.CT (fget andB orB notB)

@[expose] noncomputable def lstep (n w : Nat) (G : Nat → Nat) (k t : Nat) : Nat :=
  pcomp n w (mask w) (G k) t

@[expose] noncomputable def cstep (n w : Nat) (G GI : Nat → Nat) (k t : Nat) : Nat :=
  pcomp n w (mask w) (G k) (pcomp n w (mask w) t (GI k))

@[expose] noncomputable def genStepW (st : Nat → Nat → Nat) (T : Nat → Nat) (ew t row k c : Nat) :
    Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0,
    strictN (st k t) fun y => strictN (fget row k ew) fun j =>
      nIf(Nat.blt j c, nIf(Nat.beq (T j) y, c, nat_lit 0),
        nIf(Nat.beq j c, nIf(Nat.beq (T c) y, Nat.succ c, nat_lit 0), nat_lit 0)))

@[expose] noncomputable def pointStepW (ng : Nat) (st : Nat → Nat → Nat) (T E : Nat → Nat)
    (ew i c : Nat) : Nat :=
  strictN (T i) fun t => strictN (E i) fun row =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun r ih c => strictN (genStepW st T ew t row (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih)
      ng c

@[expose] noncomputable def runFW (ng : Nat) (st : Nat → Nat → Nat) (T E : Nat → Nat) (ew : Nat)
    (len : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih lo c => strictN (nIf(Nat.blt lo c, pointStepW ng st T E ew lo c, nat_lit 0))
      (ih (Nat.succ lo))) len

@[expose] noncomputable def runSlW (ng : Nat) (st : Nat → Nat → Nat) (T E : Nat → Nat) (ew L : Nat)
    (C : Nat → Nat) (s : Nat) : Bool :=
  Nat.beq (runFW ng st T E ew L (Nat.mul L s) (C s)) (C (Nat.succ s))

@[expose] noncomputable def distSl (N : Nat) (T S SI : Nat → Nat) (L s : Nat) : Bool :=
  allN L fun i => strictB (Nat.add (Nat.mul L s) i) fun k => strictB (S k) fun j =>
    andB (Nat.blt j N) (andB (Nat.beq (SI j) k)
      (orB (Nat.beq (Nat.succ k) N) (Nat.blt (T j) (T (S (Nat.succ k))))))

@[expose] noncomputable def pinSl (n w ng : Nat) (G T E C S SI : Nat → Nat) (N L ew s : Nat) :
    Bool :=
  andB (canonSl n w T L s)
    (andB (runSlW ng (lstep n w G) T E ew L C s) (distSl N T S SI L s))

@[expose] noncomputable def headK (n w ng : Nat) (G T C : Nat → Nat) (K N root : Nat) : Bool :=
  andB (szOK n w) (andB (allN ng fun k => canonK n w (mask w) (Nat.mul n w) (G k))
    (andB (Nat.beq (T (nat_lit 0)) root) (andB (Nat.beq (C (nat_lit 0)) (nat_lit 1))
      (Nat.beq (C K) N))))

@[expose] noncomputable def orbK (n w ng : Nat) (G GI T E S SI : Nat → Nat) (N ew root : Nat) :
    Bool :=
  andB (szOK n w) (andB (allN ng fun k => andB (canonK n w (mask w) (Nat.mul n w) (G k))
      (Nat.beq (pcomp n w (mask w) (G k) (GI k)) (pidn n w)))
    (andB (allN ng fun k => canonK n w (mask w) (Nat.mul n w) (GI k))
    (andB (Nat.beq (T (nat_lit 0)) root)
    (andB (allN N fun i => canonK n w (mask w) (Nat.mul n w) (T i))
    (andB (Nat.beq (runFW ng (cstep n w G GI) T E ew N (nat_lit 0) (nat_lit 1)) N)
      (distSl N T S SI N (nat_lit 0)))))))

@[expose] noncomputable def commPt (n w x g : Nat) : Bool :=
  allN n fun p => Nat.beq (pg w (mask w) x (pg w (mask w) g p)) (pg w (mask w) g (pg w (mask w) x p))

@[expose] noncomputable def invPt (n w x : Nat) : Bool :=
  allN n fun p => Nat.beq (pg w (mask w) x (pg w (mask w) x p)) p

@[expose] noncomputable def rPassSl (n w : Nat) (G T : Nat → Nat) (OT : Nat → Nat → Nat)
    (ON W : Nat → Nat) (L s : Nat) : Bool :=
  strictB (pidn n w) fun e => allN L fun i => strictB (Nat.add (Nat.mul L s) i) fun k =>
    strictB (T k) fun x =>
      andB (orB (notB (allN (nat_lit 3) fun j => commPt n w x (G j))) (Nat.beq x e))
        (orB (Nat.beq x e) (orB (notB (invPt n w x))
          (strictB (fget (W (Nat.shiftRight k (nat_lit 4))) (Nat.land k (nat_lit 15)) (nat_lit 13))
            fun v => strictB (Nat.shiftRight v (nat_lit 11)) fun o =>
              strictB (Nat.land v (nat_lit 2047)) fun j =>
                andB (Nat.blt o (nat_lit 4)) (andB (Nat.blt j (ON o)) (Nat.beq (OT o j) x)))))

@[expose] noncomputable def notInK (N : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  strictB x fun x => allN N fun i => notB (Nat.beq (T i) x)

@[expose] noncomputable def centK (n w N : Nat) (T : Nat → Nat) (r m : Nat) (I CT : Nat → Nat) :
    Bool :=
  strictB r fun r =>
  andB (Nat.beq (CFSG.KC.HeAutK.cntR (fun i => commPt n w (T i) r) (nat_lit 0) N) m)
    (allN m fun k => strictB (I k) fun j =>
      andB (Nat.blt j N) (andB (orB (Nat.beq (Nat.succ k) m) (Nat.blt j (I (Nat.succ k))))
        (andB (commPt n w (T j) r) (Nat.beq (CT k) (T j)))))

@[expose] noncomputable def groupK (n w m : Nat) (CT CI Q : Nat → Nat) : Bool :=
  strictB (pidn n w) fun e =>
  andB (allN m fun a => andB (canonK n w (mask w) (Nat.mul n w) (CT a))
    (andB (canonK n w (mask w) (Nat.mul n w) (CI a))
      (Nat.beq (pcomp n w (mask w) (CI a) (CT a)) e)))
  (allN m fun a => strictB (CT a) fun x => strictB (Q a) fun row => allN m fun b =>
    strictB (CT b) fun y => strictB (fget row b (nat_lit 8)) fun q =>
      andB (orB (Nat.beq a b) (notB (Nat.beq x y)))
        (andB (Nat.blt q m) (Nat.beq (CT q) (pcomp n w (mask w) x y))))

@[expose] noncomputable def classK (n w m : Nat) (CT CI P : Nat → Nat) (lab rep wit SZ ns : Nat) :
    Bool :=
  strictB (pidn n w) fun e =>
  andB (allN m fun k => strictB (P k) fun row => strictB (CT k) fun x =>
    strictB (fget lab k (nat_lit 8)) fun lk => allN m fun a =>
      strictB (fget row a (nat_lit 8)) fun p =>
        andB (Nat.blt p m) (andB (Nat.beq (CT p) (pcomp n w (mask w) (CT a)
          (pcomp n w (mask w) x (CI a)))) (Nat.beq (fget lab p (nat_lit 8)) lk)))
  (andB (allN ns fun l => strictB (fget rep l (nat_lit 8)) fun r =>
    andB (Nat.blt r m) (Nat.beq (fget lab r (nat_lit 8)) l))
  (andB (allN m fun k => strictB (fget lab k (nat_lit 8)) fun l =>
    strictB (fget wit k (nat_lit 8)) fun v =>
      andB (Nat.blt l ns) (andB (Nat.blt v m) (Nat.beq (pcomp n w (mask w) (CT v)
        (pcomp n w (mask w) (CT (fget rep l (nat_lit 8))) (CI v))) (CT k))))
  (andB (allN ns fun l => Nat.beq (CFSG.KC.HeAutK.cntR (fun k => Nat.beq (fget lab k (nat_lit 8)) l)
      (nat_lit 0) m) (fget SZ l (nat_lit 8)))
  (andB (Nat.blt (nat_lit 0) m) (andB (Nat.beq (CT (nat_lit 0)) e)
    (Nat.beq (fget lab (nat_lit 0) (nat_lit 8)) (nat_lit 0)))))))

@[expose] noncomputable def commK (n w : Nat) (T TI : Nat → Nat) (a b : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) (T a) (T b)) (TI a)) (TI b)

@[expose] noncomputable def derK (n w m : Nat) (T TI : Nat → Nat) (m' : Nat) (D PW CW : Nat → Nat)
    (IW W : Nat) : Bool :=
  strictB (pidn n w) fun e =>
  andB (allN m fun a => andB (canonK n w (mask w) (Nat.mul n w) (T a))
    (andB (canonK n w (mask w) (Nat.mul n w) (TI a))
      (Nat.beq (pcomp n w (mask w) (TI a) (T a)) e)))
  (andB (andB (Nat.blt (nat_lit 0) m') (Nat.beq (D (nat_lit 0)) e))
  (andB (allN m' fun a => andB (canonK n w (mask w) (Nat.mul n w) (D a))
    (strictB (D a) fun x => strictB (PW a) fun row =>
      andB (strictB (fget IW a (nat_lit 8)) fun q =>
          andB (Nat.blt q m') (Nat.beq (pcomp n w (mask w) (D q) x) e))
        (allN m' fun b => strictB (D b) fun y => strictB (fget row b (nat_lit 8)) fun q =>
          andB (orB (Nat.beq a b) (notB (Nat.beq x y)))
            (andB (Nat.blt q m') (Nat.beq (D q) (pcomp n w (mask w) x y))))))
  (andB (allN m fun a => strictB (CW a) fun row => allN m fun b =>
    strictB (fget row b (nat_lit 8)) fun c =>
      andB (Nat.blt c m') (Nat.beq (D c) (commK n w T TI a b)))
  (allN m' fun a => strictB (fget W a (nat_lit 32)) fun v =>
    strictB (fget v (nat_lit 0) (nat_lit 8)) fun a1 => strictB (fget v (nat_lit 1) (nat_lit 8)) fun a2 =>
    strictB (fget v (nat_lit 2) (nat_lit 8)) fun a3 => strictB (fget v (nat_lit 3) (nat_lit 8)) fun a4 =>
      andB (andB (Nat.blt a1 m) (andB (Nat.blt a2 m) (andB (Nat.blt a3 m) (Nat.blt a4 m))))
        (Nat.beq (D a) (pcomp n w (mask w) (commK n w T TI a1 a2) (commK n w T TI a3 a4)))))))

@[expose] noncomputable def normK (n w ng : Nat) (G GI : Nat → Nat) (ngS : Nat) (GS : Nat → Nat)
    (N : Nat) (T : Nat → Nat) (NW : Nat) : Bool :=
  andB (allN ng fun j => andB
      (andB (canonK n w (mask w) (Nat.mul n w) (G j)) (canonK n w (mask w) (Nat.mul n w) (GI j)))
      (Nat.beq (pcomp n w (mask w) (G j) (GI j)) (pidn n w)))
    (andB (allN ngS fun i => canonK n w (mask w) (Nat.mul n w) (GS i))
    (allN ng fun j => allN ngS fun i =>
      strictB (fget NW (Nat.mul (nat_lit 2) (Nat.add (Nat.mul ngS j) i)) (nat_lit 16)) fun p =>
      strictB (fget NW (Nat.succ (Nat.mul (nat_lit 2) (Nat.add (Nat.mul ngS j) i))) (nat_lit 16))
        fun q =>
        andB (andB (Nat.blt p N) (Nat.blt q N))
          (andB (Nat.beq (T p) (pcomp n w (mask w) (G j) (pcomp n w (mask w) (GS i) (GI j))))
            (Nat.beq (T q) (pcomp n w (mask w) (GI j) (pcomp n w (mask w) (GS i) (G j)))))))

end CFSG.KC.L34K

end
