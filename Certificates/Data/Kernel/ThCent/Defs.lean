module

public import CFSG.Certificates.Kernel.Th.S.OutS

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Loop

@[expose] noncomputable def pw24 (A e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ident24 (fun _ acc => mul24 acc A) e

@[expose] noncomputable def vpw (v X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) v (fun _ acc => vecmul acc X) e

@[expose] noncomputable def ordRank (o r X : Nat) : Bool :=
  andB (Nat.beq (vpw (nat_lit 1) X o) (nat_lit 1))
    (andB (Nat.beq (pw24 X o) ident24) (Nat.beq (OutS.rank24 (Nat.xor X ident24)) r))

@[expose] noncomputable def orAt (EB : Nat → Nat) (o r lo i : Nat) : Bool :=
  ordRank o r (DceS.mat EB (Nat.add lo i))

@[expose] noncomputable def countOR (EB : Nat → Nat) (o r lo n hi : Nat) : Nat :=
  sumBelow n hi (fun i => nIf(orAt EB o r lo i, nat_lit 1, nat_lit 0))

@[expose] noncomputable def wordM (LT : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ident24 (fun c _ ih => mul24 (DceS.let24 LT c) ih) w

@[expose] noncomputable def psOf (T : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun k ih => List.append ih (List.cons (pw24 T (Nat.succ k))
      (List.cons (Nat.xor (pw24 T (Nat.succ k)) ident24) List.nil)))

@[expose] noncomputable def par24 (z : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (Nat.land (Nat.shiftRight z k) (nat_lit 1))) (nat_lit 24)

@[expose] noncomputable def bf (B x y : Nat) : Nat := par24 (Nat.land (vecmul x B) y)

@[expose] noncomputable def memH (SV : Nat → Nat) (n w j : Nat) : Bool :=
  andB (Nat.blt j n) (Nat.beq (SV j) w)

@[expose] noncomputable def hintH (SV : Nat → Nat) (n w j : Nat) : Bool :=
  orB (memH SV n w j)
    (andB (Nat.ble j n) (andB (orB (Nat.beq j (nat_lit 0)) (Nat.blt (SV (Nat.sub j (nat_lit 1))) w))
      (orB (Nat.beq j n) (Nat.blt w (SV j)))))

@[expose] noncomputable def getN (l : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih p => Nat.rec (motive := fun _ => Nat) a (fun q _ => ih q) p) l p

@[expose] noncomputable def eqB (y x : Nat) : Nat := nIf(Nat.beq y x, nat_lit 1, nat_lit 0)

@[expose] noncomputable def codeF (FL : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun Y _ ih => Nat.add ih (eqB (vecmul x Y) x)) FL

@[expose] noncomputable def memB (SV : Nat → Nat) (n w h : Nat) : Nat :=
  nIf(memH SV n w h, nat_lit 1, nat_lit 0)

@[expose] noncomputable def compP (SV : Nat → Nat) (n B x w d h : Nat) : Nat :=
  Bool.rec (Bool.rec (memB SV n w h) (bf B x w) (Nat.beq d (nat_lit 1))) (eqB w (nat_lit 0))
    (Nat.beq d (nat_lit 0))

@[expose] noncomputable def comp (SV : Nat → Nat) (n B : Nat) (Ps FL : List Nat) (x q h : Nat) :
    Nat :=
  Bool.rec (compP SV n B x (vecmul x (getN Ps (Nat.div q (nat_lit 3)))) (Nat.mod q (nat_lit 3)) h)
    (codeF FL x) (Nat.beq q (Nat.mul (nat_lit 3) (List.length Ps)))

@[expose] noncomputable def hintOK (SV : Nat → Nat) (n : Nat) (Ps : List Nat) (x q h : Nat) :
    Bool :=
  orB (Nat.beq q (Nat.mul (nat_lit 3) (List.length Ps)))
    (orB (DceS.notB (Nat.beq (Nat.mod q (nat_lit 3)) (nat_lit 2)))
      (hintH SV n (vecmul x (getN Ps (Nat.div q (nat_lit 3)))) h))

@[expose] noncomputable def diffOK (SV R H1 : Nat → Nat) (n B : Nat) (Ps FL : List Nat) (i1 k : Nat) :
    Bool :=
  (fun s h => orB (Nat.beq s (nat_lit 63))
    (andB (Nat.ble s (Nat.mul (nat_lit 3) (List.length Ps)))
      (andB (hintOK SV n Ps (SV k) s h) (andB (hintOK SV n Ps (SV i1) s (H1 s))
        (DceS.notB (Nat.beq (comp SV n B Ps FL (SV k) s h) (comp SV n B Ps FL (SV i1) s (H1 s))))))))
    (Nat.land (R k) (nat_lit 63)) (Nat.shiftRight (R k) (nat_lit 6))

@[expose] noncomputable def allDiff (SV R H1 : Nat → Nat) (nV B : Nat) (Ps FL : List Nat)
    (i1 lo n hi : Nat) : Bool :=
  allBelow n hi (fun i => diffOK SV R H1 nV B Ps FL i1 (Nat.add lo i))

@[expose] noncomputable def selAt (R : Nat → Nat) (lo i : Nat) : Bool :=
  Nat.beq (Nat.land (R (Nat.add lo i)) (nat_lit 63)) (nat_lit 63)

@[expose] noncomputable def countSel (R : Nat → Nat) (lo n hi : Nat) : Nat :=
  sumBelow n hi (fun i => nIf(selAt R lo i, nat_lit 1, nat_lit 0))

@[expose] noncomputable def svOK (SV PI OB : Nat → Nat) (osh owd om m N lo n hi : Nat) : Bool :=
  allBelow n hi (fun i => (fun k => andB (orB (Nat.beq (Nat.succ k) N) (Nat.blt (SV k) (SV (Nat.succ k))))
      (andB (Nat.blt (PI k) m) (Nat.beq (SV k) (DceS.pt OB osh owd om (PI k)))))
    (Nat.add lo i))

@[expose] noncomputable def ptOK (SV QI OB : Nat → Nat) (osh owd om n lo m hi : Nat) : Bool :=
  allBelow m hi (fun i => (fun j => memH SV n (DceS.pt OB osh owd om j) (QI j)) (Nat.add lo i))

@[expose] noncomputable def commB (S G : Nat) : Bool := Nat.beq (mul24 S G) (mul24 G S)

@[expose] noncomputable def commAt (HB TB : Nat → Nat) (G lo i : Nat) : Bool :=
  commB (DceS.tSig HB TB (Nat.add lo i)) G

@[expose] noncomputable def countComm (HB TB : Nat → Nat) (G lo n hi : Nat) : Nat :=
  sumBelow n hi (fun i => nIf(commAt HB TB G lo i, nat_lit 1, nat_lit 0))

@[expose] noncomputable def classStep (CB : Nat → Nat) (CJ : Nat → Nat) (LT n k c : Nat) : Bool :=
  andB (Nat.blt (CJ (Nat.add (Nat.mul (nat_lit 14) k) c)) n)
    (Nat.beq (DceS.mat CB (CJ (Nat.add (Nat.mul (nat_lit 14) k) c)))
      (mul24 (mul24 (DceS.let24 LT (Nat.xor c (nat_lit 1))) (DceS.mat CB k)) (DceS.let24 LT c)))

@[expose] noncomputable def classRow (CB : Nat → Nat) (CJ : Nat → Nat) (LT n k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c acc => andB acc (classStep CB CJ LT n k c))
    (nat_lit 14)

@[expose] noncomputable def letInvOK (LT : Nat) : Bool :=
  allBelow (nat_lit 14) (nat_lit 1)
    (fun c => Nat.beq (mul24 (DceS.let24 LT c) (DceS.let24 LT (Nat.xor c (nat_lit 1)))) ident24)

@[expose] noncomputable def classOK (CB : Nat → Nat) (CJ : Nat → Nat) (LT n lo m hi : Nat) : Bool :=
  allBelow m hi (fun i => classRow CB CJ LT n (Nat.add lo i))

@[expose] noncomputable def memN (k : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec ih true (Nat.beq a k)) l

@[expose] noncomputable def eqBool (m c : Bool) : Bool := Bool.rec (DceS.notB m) m c

@[expose] noncomputable def flStep (CB : Nat → Nat) (T : Nat) (FL : List Nat) (k : Nat) : Bool :=
  eqBool (memN k FL) (commB (DceS.mat CB k) T)

@[expose] noncomputable def flOK (CB : Nat → Nat) (T : Nat) (FL : List Nat) (n hi : Nat) : Bool :=
  allBelow n hi (flStep CB T FL)

@[expose] noncomputable def formStep (B L i j : Nat) : Bool :=
  Nat.beq (bf B (vecmul (Nat.shiftLeft (nat_lit 1) i) L) (vecmul (Nat.shiftLeft (nat_lit 1) j) L))
    (bf B (Nat.shiftLeft (nat_lit 1) i) (Nat.shiftLeft (nat_lit 1) j))

@[expose] noncomputable def formL (B L : Nat) : Bool :=
  allBelow (nat_lit 576) (nat_lit 9) (fun t => formStep B L (Nat.div t (nat_lit 24)) (Nat.mod t (nat_lit 24)))

@[expose] noncomputable def formOK (B LT : Nat) : Bool :=
  allBelow (nat_lit 7) (nat_lit 1) (fun g => formL B (DceS.let24 LT (Nat.mul (nat_lit 2) g)))

@[expose] noncomputable def cLen (n i : Nat) : Nat :=
  Nat.min (Nat.sub n (Nat.mul (nat_lit 2048) i)) (nat_lit 2048)

@[expose] noncomputable def svChunk (SV PI OB : Nat → Nat) (osh owd om N i : Nat) : Bool :=
  svOK SV PI OB osh owd om N N (Nat.mul (nat_lit 2048) i) (cLen N i) (nat_lit 32)

@[expose] noncomputable def ptChunk (SV QI OB : Nat → Nat) (osh owd om N i : Nat) : Bool :=
  ptOK SV QI OB osh owd om N (Nat.mul (nat_lit 2048) i) (cLen N i) (nat_lit 32)

@[expose] noncomputable def diffChunk (SV R H1 : Nat → Nat) (N B : Nat) (Ps FL : List Nat)
    (i1 i : Nat) : Bool :=
  allDiff SV R H1 N B Ps FL i1 (Nat.mul (nat_lit 2048) i) (cLen N i) (nat_lit 32)

@[expose] noncomputable def selChunk (R : Nat → Nat) (N : Nat) (CS : List Nat) (i : Nat) : Bool :=
  Nat.beq (countSel R (Nat.mul (nat_lit 2048) i) (cLen N i) (nat_lit 32)) (getN CS i)

@[expose] noncomputable def commChunk (HB TB : Nat → Nat) (G n : Nat) (CM : List Nat) (i : Nat) :
    Bool :=
  Nat.beq (countComm HB TB G (Nat.mul (nat_lit 2048) i) (cLen n i) (nat_lit 32)) (getN CM i)

@[expose] noncomputable def allLt (l : List Nat) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (Nat.blt a n) ih) l

@[expose] noncomputable def nodupN (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a t ih => andB (DceS.notB (memN a t)) ih) l

@[expose] noncomputable def sumN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun a _ ih => Nat.add a ih) l

@[expose] noncomputable def gmN (HB GB : Nat → Nat) (j : Nat) : Nat :=
  DceS.mat HB (DceS.lo20 (DceS.e40 GB j))

@[expose] noncomputable def classMisc (LT : Nat) (CB HB GB OB SV : Nat → Nat) (osh owd om N : Nat)
    (w FL CS CM : List Nat) (o r i1 j1 Hi N1 m1 : Nat) : Bool :=
  andB (andB (andB (allLt w (nat_lit 14)) (ordRank o r (wordM LT w)))
      (andB (Nat.blt i1 N) (andB (Nat.blt j1 N) (Nat.beq (SV i1) (DceS.pt OB osh owd om j1)))))
    (andB (andB (Nat.beq (mul24 (gmN HB GB j1) Hi) ident24)
        (Nat.blt Hi (Nat.shiftLeft (nat_lit 1) (nat_lit 576))))
      (andB (andB (allLt FL (nat_lit 819)) (nodupN FL))
        (andB (flOK CB (wordM LT w) FL (nat_lit 819) (nat_lit 13))
          (andB (Nat.beq (sumN CS) N1) (Nat.beq (sumN CM) m1)))))

@[expose] noncomputable def sharedOK (LT B : Nat) (CB CJ : Nat → Nat) (om : Nat) : Bool :=
  andB (andB (Nat.blt om (Nat.shiftLeft (nat_lit 1) (nat_lit 24))) (letInvOK LT))
    (andB (formOK B LT) (classOK CB CJ LT (nat_lit 819) (nat_lit 0) (nat_lit 819) (nat_lit 13)))

@[expose] noncomputable def witOK (RB : Nat → Nat) (c rm ONE Bi GR IR Z hw hn tw tn : Nat) : Bool :=
  Nat.beq (mulB c rm (BigS.wordAB c rm ONE (RB (nat_lit 1)) (RB (nat_lit 2)) Bi hw hn) Z)
    (mulB c rm (OutS.prodWord RB c rm ONE GR IR tw tn)
      (BigS.wordAB c rm ONE (RB (nat_lit 1)) (RB (nat_lit 2)) Bi hw hn))

@[expose] noncomputable def codes4 (w n : Nat) : List Nat :=
  List.map (fun i => BigS.bitsN w (Nat.mul (nat_lit 4) i) (nat_lit 4)) (List.range n)

@[expose] noncomputable def orChunk (EB : Nat → Nat) (n o r : Nat) (OR : List Nat) (i : Nat) : Bool :=
  Nat.beq (countOR EB o r (Nat.mul (nat_lit 2048) i) (cLen n i) (nat_lit 32)) (getN OR i)

end CFSG.KC.ThCent

end
