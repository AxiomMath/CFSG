module

public import CFSG.Certificates.Kernel.Lie.CT.Core
public import CFSG.Certificates.Kernel.Local.Core

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def MUL : Nat := nat_lit 2821848294356612419217921029917578219971947684264937521152

@[expose] noncomputable def m8 (a b : Nat) : Nat := fget MUL (Nat.add (Nat.mul (nat_lit 8) a) b) (nat_lit 3)

@[expose] noncomputable def mulOK : Bool :=
  allN (nat_lit 8) fun a => allN (nat_lit 8) fun b => allN (nat_lit 8) fun c =>
    andB (Nat.beq (m8 a b) (m8 b a)) (Nat.beq (m8 a (Nat.xor b c)) (Nat.xor (m8 a b) (m8 a c)))

@[expose] noncomputable def xorN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k ih => Nat.xor (f k) ih) n

@[expose] noncomputable def foldK (n : Nat) (f : Nat → Nat → Nat) (s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s) (fun k ih s => strictN (f k s) ih) n s

@[expose] noncomputable def bitN (X i : Nat) : Nat := Nat.land (Nat.shiftRight X i) (nat_lit 1)

@[expose] noncomputable def foldUp (n : Nat) (f : Nat → Nat → Nat) (s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) s (fun k ih => strictN ih (f k)) n

@[expose] noncomputable def sqC (c e u r s : Nat) : Nat :=
  (fun u2 ur => Nat.xor (Nat.xor (m8 (m8 u2 u2) u) (m8 c (m8 ur ur))) (m8 (Nat.xor e s) r))
    (m8 u u) (m8 u r)

@[expose] noncomputable def sqK (c e v : Nat) : Nat :=
  sqC c e (fget v (nat_lit 0) (nat_lit 3)) (fget v (nat_lit 1) (nat_lit 3)) (fget v (nat_lit 2) (nat_lit 3))

@[expose] noncomputable def commC (c x1 x2 x3 z1 z2 z3 : Nat) : Nat :=
  (fun x4 z4 a b => Nat.xor (Nat.xor (Nat.xor (m8 x1 z4) (m8 x4 z1)) (m8 c (Nat.xor (m8 a a) (m8 b b))))
      (Nat.xor (m8 x3 z2) (m8 z3 x2)))
    ((fun t => m8 t t) (m8 x1 x1)) ((fun t => m8 t t) (m8 z1 z1)) (m8 x1 z2) (m8 z1 x2)

@[expose] noncomputable def commK (c x z : Nat) : Nat :=
  commC c (fget x (nat_lit 0) (nat_lit 3)) (fget x (nat_lit 1) (nat_lit 3)) (fget x (nat_lit 2) (nat_lit 3))
    (fget z (nat_lit 0) (nat_lit 3)) (fget z (nat_lit 1) (nat_lit 3)) (fget z (nat_lit 2) (nat_lit 3))

@[expose] noncomputable def lamK (p q t : Nat) : Nat :=
  Nat.xor (nIf(bit t (nat_lit 0), p, nat_lit 0)) (nIf(bit t (nat_lit 1), q, nat_lit 0))

@[expose] noncomputable def wK (p q i : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.shiftRight i (nat_lit 5))
      (Nat.shiftLeft (Nat.land (Nat.shiftRight i (nat_lit 2)) (nat_lit 7)) (nat_lit 3)))
    (Nat.shiftLeft (lamK p q (Nat.land i (nat_lit 3))) (nat_lit 6))

@[expose] noncomputable def xiK (XI m : Nat) : Nat :=
  xorN (nat_lit 8) fun j => nIf(bit m j, fget XI j (nat_lit 9), nat_lit 0)

@[expose] noncomputable def canonK (p q : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) p) (andB (Nat.blt p q) (Nat.blt q (Nat.xor p q)))

@[expose] noncomputable def PAIRS : Nat := nat_lit 2993232222289

@[expose] noncomputable def pairP (k : Nat) : Nat := fget (fget PAIRS k (nat_lit 6)) (nat_lit 0) (nat_lit 3)
@[expose] noncomputable def pairQ (k : Nat) : Nat := fget (fget PAIRS k (nat_lit 6)) (nat_lit 1) (nat_lit 3)

@[expose] noncomputable def pairsOK : Bool :=
  allN (nat_lit 8) fun p => allN (nat_lit 8) fun q =>
    Nat.beq (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (canonK p q))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
        (anyN (nat_lit 7) fun k => andB (Nat.beq (pairP k) p) (Nat.beq (pairQ k) q)))

@[expose] noncomputable def q0Rec (QT R : Nat) : Bool :=
  allN (nat_lit 256) fun m =>
    Nat.beq (sqK (fget R (nat_lit 0) (nat_lit 3)) (fget R (nat_lit 1) (nat_lit 3))
      (xiK (Nat.shiftRight R (nat_lit 76)) m)) (fget QT m (nat_lit 3))

@[expose] noncomputable def kQ0 (QT SD : Nat) : Bool :=
  allN (nat_lit 7) fun d => q0Rec QT (fget SD d (nat_lit 160))

@[expose] noncomputable def indep3K (a b c : Nat) : Bool :=
  andB (notB (Nat.beq a (nat_lit 0))) (andB (notB (Nat.beq b (nat_lit 0))) (andB (notB (Nat.beq b a))
    (andB (notB (Nat.beq c (nat_lit 0))) (andB (notB (Nat.beq c a))
      (andB (notB (Nat.beq c b)) (notB (Nat.beq c (Nat.xor a b))))))))

@[expose] noncomputable def c1Wit (c e p q x w : Nat) : Bool :=
  (fun z1 z2 z3 => andB (Nat.beq (commK c x z1) (nat_lit 0)) (andB (Nat.beq (commK c x z2) (nat_lit 0))
      (andB (Nat.beq (commK c x z3) (nat_lit 0)) (indep3K (sqK c e z1) (sqK c e z2) (sqK c e z3)))))
    (wK p q (fget w (nat_lit 0) (nat_lit 8))) (wK p q (fget w (nat_lit 1) (nat_lit 8)))
    (wK p q (fget w (nat_lit 2) (nat_lit 8)))

@[expose] noncomputable def c1Need (c e x : Nat) : Bool :=
  andB (notB (Nat.beq (fget x (nat_lit 0) (nat_lit 3)) (nat_lit 0)))
    (andB (notB (Nat.beq (fget x (nat_lit 1) (nat_lit 3)) (nat_lit 0))) (Nat.beq (sqK c e x) (nat_lit 0)))

@[expose] noncomputable def c1Step (c e p q WS i s : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), nat_lit 0,
    (fun x => nIf(c1Need c e x,
      nIf(c1Wit c e p q x (fget WS (Nat.sub s (nat_lit 1)) (nat_lit 24)), Nat.succ s, nat_lit 0), s))
    (wK p q i))

@[expose] noncomputable def c1Par (c e p q WS : Nat) : Bool :=
  notB (Nat.beq (foldK (nat_lit 256) (c1Step c e p q WS) (nat_lit 1)) (nat_lit 0))

@[expose] noncomputable def kC1 (c WT : Nat) : Bool :=
  allN (nat_lit 8) fun e => allN (nat_lit 7) fun k =>
    c1Par c e (pairP k) (pairQ k) (fget WT (Nat.add (Nat.mul (nat_lit 7) e) k) (nat_lit 1024))

@[expose] noncomputable def SPEC : Nat := nat_lit 13178008860635413019604079

@[expose] noncomputable def specK (c e p q : Nat) : Bool :=
  anyN (nat_lit 7) fun k => Nat.beq (fget SPEC k (nat_lit 12))
    (Nat.lor (Nat.lor c (Nat.shiftLeft e (nat_lit 3))) (Nat.lor (Nat.shiftLeft p (nat_lit 6)) (Nat.shiftLeft q (nat_lit 9))))

@[expose] noncomputable def allNZK (v : Nat) : Bool :=
  andB (notB (Nat.beq (fget v (nat_lit 0) (nat_lit 3)) (nat_lit 0)))
    (andB (notB (Nat.beq (fget v (nat_lit 1) (nat_lit 3)) (nat_lit 0)))
      (notB (Nat.beq (fget v (nat_lit 2) (nat_lit 3)) (nat_lit 0))))

@[expose] noncomputable def lineK (p q l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 8), l,
    nIf(Nat.blt l (nat_lit 16), Nat.shiftLeft (Nat.sub l (nat_lit 8)) (nat_lit 3),
      Nat.shiftLeft (lamK p q (Nat.sub l (nat_lit 16))) (nat_lit 6)))

@[expose] noncomputable def zMask (c e p q : Nat) : Nat :=
  orN (nat_lit 256) fun i => (fun x => nIf(andB (allNZK x) (Nat.beq (sqK c e x) (nat_lit 0)),
    Nat.shiftLeft (nat_lit 1) i, nat_lit 0)) (wK p q i)

@[expose] noncomputable def c2Pair (c p q x y : Nat) : Bool :=
  orB (Nat.beq x y) (orB (notB (Nat.beq (commK c x y) (nat_lit 0))) (orB (notB (allNZK (Nat.xor x y)))
    (anyN (nat_lit 20) fun l => (fun z => notB (Nat.beq
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (commK c x z) (nat_lit 0)))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (commK c y z) (nat_lit 0)))))
      (lineK p q l))))

@[expose] noncomputable def c2Inner (c e p q : Nat) : Bool :=
  Nat.beq (strictN (zMask c e p q) fun Z =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (CFSG.KC.Local.allBits (nat_lit 256) (fun i =>
        CFSG.KC.Local.allBits (nat_lit 256) (fun j => c2Pair c p q (wK p q i) (wK p q j)) Z) Z))
    (nat_lit 1)

@[expose] noncomputable def c2Par (c e p q : Nat) : Bool := orB (specK c e p q) (c2Inner c e p q)

@[expose] noncomputable def kC2 (c : Nat) : Bool :=
  allN (nat_lit 8) fun e => allN (nat_lit 7) fun k => c2Par c e (pairP k) (pairQ k)

@[expose] noncomputable def BID : Nat := nat_lit 1188952536082613280

@[expose] noncomputable def BIDR : Nat := nat_lit 2306970283644452880

@[expose] noncomputable def bidx (k : Nat) : Nat := fget BID k (nat_lit 8)

@[expose] noncomputable def abit (k : Nat) : Nat := fget (nat_lit 10271765) k (nat_lit 3)

@[expose] noncomputable def ALL : Nat := maskN (nat_lit 256)

@[expose] noncomputable def bmK (b : Nat) : Nat :=
  orN (nat_lit 256) fun w => nIf(bit w b, pw2 w, nat_lit 0)

@[expose] noncomputable def gAB (c p q a b : Nat) : Nat := commK c (wK p q (pw2 a)) (wK p q (pw2 b))

@[expose] noncomputable def maK (c p q : Nat) : Nat :=
  orN (nat_lit 24) fun ix => (fun a t => Nat.shiftLeft
      (xorN (nat_lit 8) fun b => nIf(bit (gAB c p q a b) t, bmK b, nat_lit 0))
      (Nat.mul (nat_lit 256) ix))
    (Nat.div ix (nat_lit 3)) (Nat.mod ix (nat_lit 3))

@[expose] noncomputable def xwK (MA w : Nat) : Nat :=
  xorN (nat_lit 8) fun a => nIf(bit w a, fget MA a (nat_lit 768), nat_lit 0)

@[expose] noncomputable def cmK (c e p q : Nat) : Nat :=
  orN (nat_lit 256) fun i => Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul (nat_lit 256) (sqK c e (wK p q i))) i)

@[expose] noncomputable def ttK (c p q : Nat) : Nat :=
  orN (nat_lit 64) fun jk => Nat.shiftLeft
    (gAB c p q (abit (Nat.div jk (nat_lit 8))) (abit (Nat.mod jk (nat_lit 8)))) (Nat.mul (nat_lit 3) jk)

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def candK (TT XS k C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) C (fun j ih =>
    (fun v X => Nat.land ih (Nat.land
        (nIf(bit v (nat_lit 0), fget X (nat_lit 0) (nat_lit 256), Nat.xor ALL (fget X (nat_lit 0) (nat_lit 256))))
        (Nat.land
          (nIf(bit v (nat_lit 1), fget X (nat_lit 1) (nat_lit 256), Nat.xor ALL (fget X (nat_lit 1) (nat_lit 256))))
          (nIf(bit v (nat_lit 2), fget X (nat_lit 2) (nat_lit 256), Nat.xor ALL (fget X (nat_lit 2) (nat_lit 256)))))))
      (fget TT (Nat.add (Nat.mul (nat_lit 8) j) k) (nat_lit 3))
      (fget XS (Nat.sub (Nat.sub k j) (nat_lit 1)) (nat_lit 768))) k

@[expose] noncomputable def c3Ext (MA TT LV : Nat) (d : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ A _ => Nat.beq A BIDR)
    (fun _ ih k A XS => strictB (candK TT XS k (fget LV k (nat_lit 256))) fun C =>
      CFSG.KC.Local.allBits (nat_lit 256) (fun w =>
        ih (Nat.succ k) (Nat.lor (Nat.shiftLeft A (nat_lit 8)) w)
          (Nat.lor (Nat.shiftLeft XS (nat_lit 768)) (xwK MA w))) C)
    d

@[expose] noncomputable def radK (MA : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ALL (fun i ih => Nat.land ih (Nat.xor ALL (fget MA i (nat_lit 256))))
    (nat_lit 24)

@[expose] noncomputable def BM : Nat := orN (nat_lit 8) fun b => Nat.shiftLeft (bmK b) (Nat.mul (nat_lit 256) b)

@[expose] noncomputable def gtK (c p q : Nat) : Nat :=
  orN (nat_lit 64) fun ab => Nat.shiftLeft (gAB c p q (Nat.div ab (nat_lit 8)) (Nat.mod ab (nat_lit 8)))
    (Nat.mul (nat_lit 3) ab)

@[expose] noncomputable def cmQ (c e p q GT BMS : Nat) : Nat :=
  strictN (orN (nat_lit 3) fun t => Nat.shiftLeft (Nat.xor
      (xorN (nat_lit 8) fun a => nIf(bit (sqK c e (wK p q (pw2 a))) t, fget BMS a (nat_lit 256), nat_lit 0))
      (xorN (nat_lit 64) fun ab => (fun a b => nIf(andB (Nat.blt a b)
          (bit (fget GT (Nat.add (Nat.mul (nat_lit 8) a) b) (nat_lit 3)) t),
        Nat.land (fget BMS a (nat_lit 256)) (fget BMS b (nat_lit 256)), nat_lit 0))
        (Nat.div ab (nat_lit 8)) (Nat.mod ab (nat_lit 8))))
    (Nat.mul (nat_lit 256) t)) fun QB =>
  orN (nat_lit 8) fun v => Nat.shiftLeft (Nat.land
      (nIf(bit v (nat_lit 0), fget QB (nat_lit 0) (nat_lit 256), Nat.xor ALL (fget QB (nat_lit 0) (nat_lit 256))))
      (Nat.land (nIf(bit v (nat_lit 1), fget QB (nat_lit 1) (nat_lit 256), Nat.xor ALL (fget QB (nat_lit 1) (nat_lit 256))))
        (nIf(bit v (nat_lit 2), fget QB (nat_lit 2) (nat_lit 256), Nat.xor ALL (fget QB (nat_lit 2) (nat_lit 256))))))
    (Nat.mul (nat_lit 256) v)

@[expose] noncomputable def perpK (MA y : Nat) : Nat :=
  strictN (xwK MA y) fun X => Nat.xor ALL (Nat.lor (fget X (nat_lit 0) (nat_lit 256))
    (Nat.lor (fget X (nat_lit 1) (nat_lit 256)) (fget X (nat_lit 2) (nat_lit 256))))

@[expose] noncomputable def addCnt (S m : Nat) : Nat :=
  Nat.land (foldUp (nat_lit 9) (fun i s => (fun ci cy => Nat.lor
      (Nat.xor (Nat.land s (maskN (nat_lit 2304))) (Nat.shiftLeft cy (Nat.mul (nat_lit 256) i)))
      (Nat.shiftLeft (Nat.land ci cy) (nat_lit 2304)))
      (fget s i (nat_lit 256)) (Nat.shiftRight s (nat_lit 2304)))
    (Nat.lor S (Nat.shiftLeft m (nat_lit 2304)))) (maskN (nat_lit 2304))

@[expose] noncomputable def n0K (MA Z : Nat) : Nat :=
  CFSG.KC.Local.foldBits (nat_lit 256) (fun y S => addCnt S (perpK MA y)) Z (nat_lit 0)

@[expose] noncomputable def eqCnt (CN v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ALL (fun i ih => Nat.land ih
    (nIf(bit v i, fget CN i (nat_lit 256), Nat.xor ALL (fget CN i (nat_lit 256))))) (nat_lit 9)

@[expose] noncomputable def cntAt (CN x : Nat) : Nat :=
  orN (nat_lit 9) fun i => Nat.shiftLeft (bitN (fget CN i (nat_lit 256)) x) i

@[expose] noncomputable def lvK (c e p q CM CN : Nat) : Nat :=
  orN (nat_lit 8) fun k => Nat.shiftLeft (Nat.land (fget CM (sqK c e (wK p q (bidx k))) (nat_lit 256))
    (eqCnt CN (cntAt CN (bidx k)))) (Nat.mul (nat_lit 256) k)

@[expose] noncomputable def c3Par (c e p q MA TT RAD GT BMS : Nat) : Bool :=
  strictB (cmQ c e p q GT BMS) fun CM => andB (Nat.beq (Nat.land RAD (fget CM (nat_lit 0) (nat_lit 256))) (nat_lit 1))
    (strictB (n0K MA (fget CM (nat_lit 0) (nat_lit 256))) fun CN => strictB (lvK c e p q CM CN) fun LV =>
      c3Ext MA TT LV (nat_lit 8) (nat_lit 0) (nat_lit 0) (nat_lit 0))

@[expose] noncomputable def c3Pair (c k : Nat) : Bool :=
  (fun p q => strictB (maK c p q) fun MA => strictB (ttK c p q) fun TT => strictB (radK MA) fun RAD =>
    strictB (gtK c p q) fun GT => strictB BM fun BMS =>
    allN (nat_lit 8) fun e => c3Par c e p q MA TT RAD GT BMS) (pairP k) (pairQ k)

@[expose] noncomputable def linAppK (R t : Nat) : Nat :=
  xorN (nat_lit 3) fun k => nIf(bit t k, fget R k (nat_lit 3), nat_lit 0)

@[expose] noncomputable def linCompK (R S : Nat) : Nat :=
  orN (nat_lit 3) fun k => Nat.shiftLeft (linAppK R (fget S k (nat_lit 3))) (Nat.mul (nat_lit 3) k)

@[expose] noncomputable def LINID : Nat := nat_lit 273

@[expose] noncomputable def glK (R : Nat) : Bool :=
  indep3K (fget R (nat_lit 0) (nat_lit 3)) (fget R (nat_lit 1) (nat_lit 3)) (fget R (nat_lit 2) (nat_lit 3))

@[expose] noncomputable def rhoK (R : Nat) : Nat :=
  orN (nat_lit 9) fun ij => Nat.shiftLeft
    (bitN (fget R (Nat.mod ij (nat_lit 3)) (nat_lit 3)) (Nat.div ij (nat_lit 3))) ij

@[expose] noncomputable def bmulK (A B : Nat) : Nat :=
  orN (nat_lit 9) fun ij => (fun i j => Nat.shiftLeft
      (xorN (nat_lit 3) fun k => Nat.land (bitN A (Nat.add (Nat.mul (nat_lit 3) i) k))
        (bitN B (Nat.add (Nat.mul (nat_lit 3) k) j))) ij)
    (Nat.div ij (nat_lit 3)) (Nat.mod ij (nat_lit 3))

@[expose] noncomputable def slToMatK (m : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft (bitN m (nat_lit 0)) (nat_lit 1)) (Nat.shiftLeft (bitN m (nat_lit 1)) (nat_lit 2)))
      (Nat.lor (Nat.shiftLeft (bitN m (nat_lit 2)) (nat_lit 3)) (Nat.shiftLeft (bitN m (nat_lit 3)) (nat_lit 5))))
    (Nat.lor (Nat.lor (Nat.shiftLeft (bitN m (nat_lit 4)) (nat_lit 6)) (Nat.shiftLeft (bitN m (nat_lit 5)) (nat_lit 7)))
      (Nat.lor (Nat.lor (bitN m (nat_lit 6)) (Nat.shiftLeft (bitN m (nat_lit 7)) (nat_lit 8)))
        (Nat.shiftLeft (Nat.xor (bitN m (nat_lit 6)) (bitN m (nat_lit 7))) (nat_lit 4))))

@[expose] noncomputable def matToSlK (A : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (bitN A (nat_lit 1)) (Nat.shiftLeft (bitN A (nat_lit 2)) (nat_lit 1)))
      (Nat.lor (Nat.shiftLeft (bitN A (nat_lit 3)) (nat_lit 2)) (Nat.shiftLeft (bitN A (nat_lit 5)) (nat_lit 3))))
    (Nat.lor (Nat.lor (Nat.shiftLeft (bitN A (nat_lit 6)) (nat_lit 4)) (Nat.shiftLeft (bitN A (nat_lit 7)) (nat_lit 5)))
      (Nat.lor (Nat.shiftLeft (bitN A (nat_lit 0)) (nat_lit 6)) (Nat.shiftLeft (bitN A (nat_lit 8)) (nat_lit 7))))

@[expose] noncomputable def adK (R I : Nat) : Nat :=
  strictN (rhoK R) fun P => strictN (rhoK I) fun Q =>
    orN (nat_lit 8) fun k => Nat.shiftLeft (matToSlK (bmulK (bmulK P (slToMatK (pw2 k))) Q)) (Nat.mul (nat_lit 8) k)

@[expose] noncomputable def maskAppK (A m : Nat) : Nat :=
  xorN (nat_lit 8) fun k => nIf(bit m k, fget A k (nat_lit 8), nat_lit 0)

@[expose] noncomputable def xAppK (X p q v : Nat) : Nat :=
  (fun u r s => (fun s1 s2 =>
      xorN (nat_lit 8) fun k => nIf(
        bIf(Nat.beq (Nat.mod k (nat_lit 3)) (nat_lit 0), bit u (Nat.div k (nat_lit 3)),
          bIf(Nat.beq (Nat.mod k (nat_lit 3)) (nat_lit 1), bit r (Nat.div k (nat_lit 3)),
            bIf(Nat.beq (Nat.div k (nat_lit 3)) (nat_lit 0), s1, s2))),
        fget X k (nat_lit 8), nat_lit 0))
      (orB (Nat.beq s p) (Nat.beq s (Nat.xor p q))) (orB (Nat.beq s q) (Nat.beq s (Nat.xor p q))))
    (fget v (nat_lit 0) (nat_lit 3)) (fget v (nat_lit 1) (nat_lit 3)) (fget v (nat_lit 2) (nat_lit 3))

@[expose] noncomputable def lamMemK (p q s : Nat) : Bool :=
  orB (Nat.beq s (nat_lit 0)) (orB (Nat.beq s p) (orB (Nat.beq s q) (Nat.beq s (Nat.xor p q))))

@[expose] noncomputable def kS0 (SD INV : Nat) : Bool :=
  andB (allN (nat_lit 7) fun d => andB (Nat.beq (fget (fget SD d (nat_lit 160)) (nat_lit 0) (nat_lit 12)) (fget SPEC d (nat_lit 12)))
    (canonK (fget (fget SD d (nat_lit 160)) (nat_lit 2) (nat_lit 3)) (fget (fget SD d (nat_lit 160)) (nat_lit 3) (nat_lit 3))))
  (andB (allN (nat_lit 512) fun R => orB (notB (glK R)) ((fun I =>
      andB (glK I) (andB (Nat.beq (linCompK R I) LINID) (andB (Nat.beq (linCompK I R) LINID)
        (andB (Nat.beq (bmulK (rhoK R) (rhoK I)) LINID) (Nat.beq (bmulK (rhoK I) (rhoK R)) LINID)))))
      (fget INV R (nat_lit 9))))
  (andB (allN (nat_lit 256) fun m => Nat.beq (matToSlK (slToMatK m)) m)
  (andB (allN (nat_lit 512) fun R => orB (notB (glK R)) (Nat.beq ((fun I => strictN (adK R I) fun A =>
      strictN (rhoK R) fun P => strictN (rhoK I) fun Q => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
        (allN (nat_lit 8) fun k => Nat.beq (slToMatK (maskAppK A (pw2 k))) (bmulK (bmulK P (slToMatK (pw2 k))) Q)))
      (fget INV R (nat_lit 9))) (nat_lit 1)))
  (allN (nat_lit 7) fun d => (fun Rd => (fun p q X XI =>
      andB (allN (nat_lit 8) fun a => Nat.beq (xiK XI (xAppK X p q (wK p q (pw2 a)))) (wK p q (pw2 a)))
        (allN (nat_lit 8) fun k => andB (Nat.beq (xAppK X p q (xiK XI (pw2 k))) (pw2 k))
          (lamMemK p q (fget (xiK XI (pw2 k)) (nat_lit 2) (nat_lit 3)))))
      (fget Rd (nat_lit 2) (nat_lit 3)) (fget Rd (nat_lit 3) (nat_lit 3))
      (fget (Nat.shiftRight Rd (nat_lit 12)) (nat_lit 0) (nat_lit 64)) (Nat.shiftRight Rd (nat_lit 76)))
    (fget SD d (nat_lit 160))))))

@[expose] noncomputable def kS1 (INV Rd : Nat) : Bool :=
  (fun c e p q X XI => allN (nat_lit 512) fun R => orB (notB (glK R))
      (Nat.beq (strictN (adK R (fget INV R (nat_lit 9))) fun A => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
        (allN (nat_lit 8) fun a => allN (Nat.succ a) fun b => (fun w =>
          Nat.beq (sqK c e (xiK XI (maskAppK A (xAppK X p q w)))) (linAppK R (sqK c e w)))
          (wK p q (Nat.lor (pw2 a) (pw2 b))))) (nat_lit 1)))
    (fget Rd (nat_lit 0) (nat_lit 3)) (fget Rd (nat_lit 1) (nat_lit 3)) (fget Rd (nat_lit 2) (nat_lit 3))
    (fget Rd (nat_lit 3) (nat_lit 3)) (fget (Nat.shiftRight Rd (nat_lit 12)) (nat_lit 0) (nat_lit 64))
    (Nat.shiftRight Rd (nat_lit 76))

@[expose] noncomputable def invoK (R : Nat) : Bool :=
  andB (glK R) (andB (notB (Nat.beq R LINID)) (Nat.beq (linCompK R R) LINID))

@[expose] noncomputable def invlOK (INVL : Nat) : Bool :=
  allN (nat_lit 512) fun R => Nat.beq (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (invoK R))
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (anyN (nat_lit 21) fun i => Nat.beq (fget INVL i (nat_lit 9)) R))

@[expose] noncomputable def fourK (R1 R2 : Nat) : Bool :=
  andB (notB (Nat.beq R1 R2)) (Nat.beq (linCompK R1 R2) (linCompK R2 R1))

@[expose] noncomputable def kS2a (INV INVL : Nat) : Bool :=
  andB (invlOK INVL) (allN (nat_lit 21) fun i => allN (nat_lit 21) fun j =>
    (fun R1 R2 => orB (notB (fourK R1 R2))
      (Nat.beq (strictN (adK R1 (fget INV R1 (nat_lit 9))) fun A1 => strictN (adK R2 (fget INV R2 (nat_lit 9))) fun A2 =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.ble (sumN (nat_lit 256) fun m =>
          Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
            (andB (Nat.beq (maskAppK A1 m) m) (Nat.beq (maskAppK A2 m) m))) (nat_lit 4))) (nat_lit 1)))
      (fget INVL i (nat_lit 9)) (fget INVL j (nat_lit 9)))

@[expose] noncomputable def kS2b (INVL : Nat) : Bool :=
  andB (invlOK INVL) (allN (nat_lit 21) fun i => allN (nat_lit 21) fun j =>
    (fun R1 R2 => orB (notB (fourK R1 R2)) (allN (nat_lit 512) fun R => orB (notB (glK R))
      (orB (notB (Nat.beq (linCompK R R1) (linCompK R1 R))) (orB (notB (Nat.beq (linCompK R R2) (linCompK R2 R)))
        (orB (Nat.beq R LINID) (orB (Nat.beq R R1) (orB (Nat.beq R R2) (Nat.beq R (linCompK R1 R2)))))))))
      (fget INVL i (nat_lit 9)) (fget INVL j (nat_lit 9)))

@[expose] noncomputable def bindFin8 (L : List (Fin 8)) (T n : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
    (fun a _ ih i => andB (Nat.beq a.val (fget T i (nat_lit 3))) (ih (Nat.succ i))) L (nat_lit 0)

@[expose] noncomputable def bindMul (mt : Array (Fin 8)) : Bool := bindFin8 mt.toList MUL (nat_lit 64)

@[expose] noncomputable def bindQ (qt : List (Fin 8)) (QT : Nat) : Bool := bindFin8 qt QT (nat_lit 256)

@[expose] noncomputable def packV (v : Fin 8 × Fin 8 × Fin 8) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun u rs => Prod.rec (motive := fun _ => Nat)
    (fun r s => Nat.lor u.val (Nat.lor (Nat.shiftLeft r.val (nat_lit 3)) (Nat.shiftLeft s.val (nat_lit 6)))) rs) v

@[expose] noncomputable def bindList {α : Type} (f : α → Nat) (L : List α) (T w n : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
    (fun a _ ih i => andB (Nat.beq (f a) (fget T i w)) (ih (Nat.succ i))) L (nat_lit 0)

@[expose] noncomputable def pack4 (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun c t => Prod.rec (motive := fun _ => Nat) (fun e t =>
    Prod.rec (motive := fun _ => Nat) (fun p q => Nat.lor (Nat.lor c.val (Nat.shiftLeft e.val (nat_lit 3)))
      (Nat.lor (Nat.shiftLeft p.val (nat_lit 6)) (Nat.shiftLeft q.val (nat_lit 9)))) t) t) t

@[expose] noncomputable def sdRecOK (d : (Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List (Fin 8 × Fin 8 × Fin 8))
    (R : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun t xs => Prod.rec (motive := fun _ => Bool) (fun X Xi =>
    andB (Nat.beq (pack4 t) (fget R (nat_lit 0) (nat_lit 12)))
      (andB (bindList (fun n => n) X (Nat.shiftRight R (nat_lit 12)) (nat_lit 8) (nat_lit 8))
        (andB (List.rec (motive := fun _ => Bool) true (fun n _ ih => andB (Nat.blt n (nat_lit 256)) ih) X)
          (bindList packV Xi (Nat.shiftRight R (nat_lit 76)) (nat_lit 9) (nat_lit 8))))) xs) d

@[expose] noncomputable def bindSD (sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List (Fin 8 × Fin 8 × Fin 8)))
    (SD : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 7))
    (fun d _ ih i => andB (sdRecOK d (fget SD i (nat_lit 160))) (ih (Nat.succ i))) sd (nat_lit 0)

@[expose] noncomputable def bindSpec (sl : List (Fin 8 × Fin 8 × Fin 8 × Fin 8)) : Bool :=
  bindList pack4 sl SPEC (nat_lit 12) (nat_lit 7)

end CFSG.KC.GMS

end
