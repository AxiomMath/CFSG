module

public import Certificates.Data.Kernel.LocalQT.PermW
public import Certificates.Data.Kernel.LocalQT.Base

public section

namespace CFSG.KC.LQT.PP

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC

@[expose] noncomputable def appK (a b : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) b (fun x _ ih => List.cons x ih) a

@[expose] noncomputable def flatK (cs : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun c _ ih => appK c ih) cs

@[expose] noncomputable def chunksK (c : Array (Array Nat)) : List Nat :=
  flatK (List.rec (motive := fun _ => List (List Nat)) [] (fun a _ ih => List.cons a.toList ih)
    c.toList)

@[expose] noncomputable def codeK (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add x (Nat.shiftLeft ih w)) l

@[expose] noncomputable def letLs (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def allR (lo len : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => andB (f (Nat.add lo j)) ih) len

@[expose] noncomputable def bitK (m i : Nat) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i))

@[expose] noncomputable def maskL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor (Nat.shiftLeft 1 x) ih) l

@[expose] noncomputable def sumL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add x ih) l

@[expose] noncomputable def nthP (l : List (Nat × Nat)) (i : Nat) : Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => Prod.mk 0 0)
    (fun x _ ih j => Bool.rec (motive := fun _ => Nat × Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i

@[expose] noncomputable def getT (L : List (List Nat)) (j : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Bool.rec (motive := fun _ => List Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) L j

@[expose] noncomputable def headK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ _ => x) l

@[expose] noncomputable def tailK (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) l

@[expose] noncomputable def incK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih m => andB (Nat.ble m x) (ih (Nat.succ x))) l 0

@[expose] noncomputable def treeK (N : Nat) (P Gn : List Nat) : Bool :=
  andB (Nat.beq (lenA P) N) (andB (Nat.beq (lenA Gn) N)
    (List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ _ => true)
      (fun p _ ih gs i => List.rec (motive := fun _ => Bool) false
        (fun g gs' _ => CFSG.KC.LQT.P.letB i fun i' =>
          andB (impB (Nat.blt 0 i') (andB (Nat.blt p i') (Nat.blt g 2))) (ih gs' (Nat.succ i')))
        gs) P Gn 0))

@[expose] noncomputable def invK (n w : Nat) (ta tb tai tbi : List Nat) : Bool :=
  allBs [tabL n ta, tabL n tb, tabL n tai, tabL n tbi,
    Nat.beq (mulW n w (codeK w tai) (codeK w ta)) (oneW n w),
    Nat.beq (mulW n w (codeK w tbi) (codeK w tb)) (oneW n w)]

@[expose] noncomputable def aszK (N : Nat) (Aa Ab : List Nat) : Bool :=
  andB (Nat.ble N (lenA Aa)) (Nat.ble N (lenA Ab))

@[expose] noncomputable def xsK (N : Nat) (XS : List (List Nat)) : Bool :=
  andB (Nat.blt 0 (lenA XS)) (andB (List.rec (motive := fun _ => Bool) false
      (fun l _ _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l) XS)
    (allA XS fun l => allL l fun x => Nat.blt x N))

@[expose] noncomputable def permK (N : Nat) (l : List Nat) : Bool :=
  andB (tabL N l) (Nat.beq (maskL l) (Nat.sub (Nat.shiftLeft 1 N) 1))

@[expose] noncomputable def slpM (mf : Nat → Nat → Nat) (a b : Nat) (prog : List (Nat × Nat)) :
    List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun p _ ih acc => letLs (mf (nodeK acc p.1) (nodeK acc p.2)) fun y =>
      ih (List.cons y acc)) prog [b, a]

@[expose] noncomputable def slpW (n w a b : Nat) (prog : List (Nat × Nat)) : List Nat :=
  slpM (mulW n w) a b prog

@[expose] noncomputable def enumR (n w : Nat) (R : List Nat) (qp : List (Nat × Nat))
    (k fuel d : Nat) (RL : List Nat) : Bool :=
  andB (allA qp fun p => andB (Nat.blt p.1 (lenA R)) (Nat.blt p.2 (lenA R)))
  (andB (allA qp fun p => Nat.beq (mulW n w (nodeK R p.2) (nodeK R p.1)) (oneW n w))
  ((fun G => allBs [closedG (mulW n w) (oneW n w) G (bfsG (mulW n w) (oneW n w) G d),
      Nat.beq (bfsG (mulW n w) (oneW n w) G d).size (Nat.pow 2 k),
      Nat.ble (bfsG (mulW n w) (oneW n w) G d).size fuel,
      eqL (bfsG (mulW n w) (oneW n w) G d).elems RL])
    (List.rec (motive := fun _ => List Nat) [] (fun p _ ih => List.cons (nodeK R p.1) ih) qp)))

@[expose] noncomputable def enumK (n w : Nat) (ta tb : List Nat) (prog : List (Nat × Nat))
    (qp : List (Nat × Nat)) (k fuel d : Nat) (RL : List Nat) : Bool :=
  andB (tabL n ta) (andB (tabL n tb) (andB (slpOKK prog 2)
    (enumR n w (slpW n w (codeK w ta) (codeK w tb) prog) qp k fuel d RL)))

@[expose] noncomputable def treeOf (RL : List Nat) : NT :=
  List.rec (motive := fun _ => NT) NT.lf (fun x _ ih => insT ih x) RL

@[expose] noncomputable def rtAt (n w W : Nat) (ca cb PK GK : Nat) (RF : Nat → Nat) (i : Nat) :
    Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Nat.beq (RF i) (mulW n w (Bool.rec (motive := fun _ => Nat) cb ca (Nat.beq (imgW W GK i) 0))
      (RF (imgW W PK i))))
    (Nat.beq (RF 0) (oneW n w)) (Nat.beq i 0)

@[expose] noncomputable def edgeAt (n w W N : Nat) (ca cb AK BK : Nat) (RF : Nat → Nat) (T : NT)
    (i : Nat) : Bool :=
  CFSG.KC.LQT.P.letB (imgW W AK i) fun ai => CFSG.KC.LQT.P.letB (imgW W BK i) fun bi =>
  andB (Nat.blt ai N) (andB (Nat.blt bi N)
    (andB (memT T (mulW n w (invW n w (RF ai)) (mulW n w ca (RF i))))
      (memT T (mulW n w (invW n w (RF bi)) (mulW n w cb (RF i))))))

@[expose] noncomputable def edgeChunk (n w W N : Nat) (ca cb AK BK PK GK : Nat) (RF : Nat → Nat)
    (T : NT) (lo len : Nat) : Bool :=
  allR lo len fun i => andB (rtAt n w W ca cb PK GK RF i) (edgeAt n w W N ca cb AK BK RF T i)

@[expose] noncomputable def compK (N W c s t : Nat) : Bool :=
  allR 0 N fun i => Nat.beq (imgW W c i) (imgW W s (imgW W t i))

@[expose] noncomputable def idK (N W c : Nat) : Bool :=
  allR 0 N fun i => Nat.beq (imgW W c i) i

@[expose] noncomputable def slpChk (N W : Nat) (TF : Nat → Nat) (prog : List (Nat × Nat))
    (j : Nat) : Bool :=
  andB (Nat.ble 2 j)
    ((fun p => compK N W (TF j) (TF p.1) (TF p.2)) (nthP prog (Nat.sub j 2)))

@[expose] noncomputable def slpNeedK (prog : List (Nat × Nat)) (S : List Nat) : Bool :=
  allL S fun j => andB (Nat.ble 2 j) (andB (Nat.blt j (Nat.add (lenA prog) 2))
    ((fun p => andB (orB (Nat.blt p.1 2) (anyL S (Nat.beq p.1)))
      (orB (Nat.blt p.2 2) (anyL S (Nat.beq p.2)))) (nthP prog (Nat.sub j 2))))

@[expose] noncomputable def omChk (N W : Nat) (TF MF : Nat → Nat) (PK GK x : Nat) : Bool :=
  andB (Nat.blt 0 x) (andB (Nat.blt x N)
    (compK N W (MF x) (Bool.rec (motive := fun _ => Nat) (TF 1) (TF 0) (Nat.beq (imgW W GK x) 0))
      (MF (imgW W PK x))))

@[expose] noncomputable def needP (W PK : Nat) (M : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun x _ ih seen => andB (andB (Nat.blt 0 x)
      (CFSG.KC.LQT.P.letB (imgW W PK x) fun p => orB (Nat.beq p 0) (anyL seen (Nat.beq p))))
      (ih (List.cons x seen)))
    M []

@[expose] noncomputable def qpK (TF : Nat → Nat) (qp : List (Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun p _ ih => List.cons (TF p.1) ih) qp

@[expose] noncomputable def repsAt (N W : Nat) (RC : List Nat) (RPK RIK QPK QGK DPK : Nat)
    (REPS OML : List Nat) (i : Nat) : Bool :=
  CFSG.KC.LQT.P.letB (imgW W RPK i) fun r => CFSG.KC.LQT.P.letB (imgW W RIK i) fun ri =>
  CFSG.KC.LQT.P.letB (getK OML ri) fun M =>
  andB (Nat.blt r N) (andB (Nat.beq (getK REPS ri) r) (andB (bitK M i)
    (andB (allL RC fun g => bitK M (imgW W g i))
      (Bool.rec (motive := fun _ => Bool)
        (CFSG.KC.LQT.P.letB (imgW W QPK i) fun q => CFSG.KC.LQT.P.letB (imgW W QGK i) fun gi =>
          andB (Nat.blt gi (lenA RC)) (andB (Nat.beq (imgW W (getK RC gi) q) i)
            (andB (bitK M q) (Nat.blt (imgW W DPK q) (imgW W DPK i)))))
        (Nat.beq (imgW W DPK i) 0) (Nat.beq i r)))))

@[expose] noncomputable def repsChunk (N W : Nat) (RC : List Nat) (RPK RIK QPK QGK DPK : Nat)
    (REPS OML : List Nat) (lo len : Nat) : Bool :=
  allR lo len (repsAt N W RC RPK RIK QPK QGK DPK REPS OML)

@[expose] noncomputable def repsSumK (N : Nat) (REPS OML : List Nat) : Bool :=
  andB (Nat.beq (sumL OML) (Nat.sub (Nat.shiftLeft 1 N) 1))
    (andB (Nat.beq (lenA OML) (lenA REPS)) (incK REPS))

@[expose] noncomputable def smallK (N W : Nat) (GS : List Nat) (B : Nat) (PT : List Nat) : Bool :=
  allBs [Nat.beq (maskL PT) B, allL PT (fun p => Nat.blt p N),
    allL PT (fun p => allL GS fun g => bitK B (imgW W g p)),
    List.rec (motive := fun _ => List Nat → Bool) (fun seen => Nat.blt 0 (lenA seen))
      (fun p _ ih seen => andB
        (List.rec (motive := fun _ => Bool) (Nat.beq p 0)
          (fun _ _ _ => anyL seen fun q => anyL GS fun g => Nat.beq (imgW W g q) p) seen)
        (ih (List.cons p seen))) PT []]

@[expose] noncomputable def fullK (N W : Nat) (GS : List Nat) (RPK : Nat) (REPS E : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun QV => Nat.beq QV (maskL REPS))
    (fun e _ ih QV => CFSG.KC.LQT.P.letB (Nat.shiftRight e 3) fun y =>
      CFSG.KC.LQT.P.letB (Nat.land e 7) fun g =>
      andB (andB (Nat.blt y N) (andB (Nat.blt g (lenA GS)) (bitK QV (imgW W RPK y))))
        (ih (Nat.lor QV (Nat.shiftLeft 1 (imgW W RPK (imgW W (getK GS g) y))))))
    E (Nat.shiftLeft 1 (imgW W RPK 0))

@[expose] noncomputable def orbChk (N W : Nat) (GS : List Nat) (RPK : Nat) (REPS : List Nat)
    (B : Nat) (C : List Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (smallK N W GS B C) (fullK N W GS RPK REPS C)
    (Nat.beq B (Nat.sub (Nat.shiftLeft 1 N) 1))

@[expose] noncomputable def gensK (RC : List Nat) (MF : Nat → Nat) (xs : List Nat) : List Nat :=
  appK RC (List.rec (motive := fun _ => List Nat) [] (fun x _ ih => List.cons (MF x) ih) xs)

@[expose] noncomputable def blockK (N W : Nat) (RC : List Nat) (MF : Nat → Nat) (RPK : Nat)
    (REPS BM : List Nat) (BWL XS : List (List Nat)) (h : Nat) : Bool :=
  orbChk N W (gensK RC MF (getT XS h)) RPK REPS (getK BM h) (getT BWL h)

@[expose] noncomputable def pairK (N W : Nat) (RC : List Nat) (MF : Nat → Nat) (RPK : Nat)
    (REPS BM : List Nat) (PWL XS : List (List Nat)) (i : Nat) : Bool :=
  (fun h c C => andB (Nat.blt (headK C) (lenA BM))
      (orbChk N W (appK (gensK RC MF (getT XS h)) [MF (getK REPS c)]) RPK REPS
        (getK BM (headK C)) (tailK C)))
    (Nat.div i (lenA REPS)) (Nat.mod i (lenA REPS)) (getT PWL i)

@[expose] noncomputable def popK (N m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc
    (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i))))) N

@[expose] noncomputable def shapeK (N : Nat) (BM : List Nat) (h1 h2 : Nat) : Bool :=
  (fun (full : Nat → Bool) (sub : Nat → Nat → Bool) => allBs
    [Nat.blt h1 (lenA BM), Nat.blt h2 (lenA BM), notB (full (getK BM h1)), notB (full (getK BM h2)),
     notB (Nat.beq (popK N (getK BM h1)) (popK N (getK BM h2))),
     allL BM (fun b => impB (sub (getK BM h1) b) (orB (sub b (getK BM h1)) (full b))),
     allL BM (fun b => impB (sub (getK BM h2) b) (orB (sub b (getK BM h2)) (full b))),
     allL BM (fun b => impB (notB (full b)) (orB (sub b (getK BM h1)) (sub b (getK BM h2))))])
    (fun m => Nat.beq m (Nat.sub (Nat.shiftLeft 1 N) 1)) (fun a b => Nat.beq (Nat.land a b) a)

end CFSG.KC.LQT.PP

end
