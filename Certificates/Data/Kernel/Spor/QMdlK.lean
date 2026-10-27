module

public import Certificates.Data.Kernel.Spor.HypK

public section

namespace CFSG.KS.QMdlK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PSearch CFSG.KS.HypK CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def add5 (a b : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (dg3 a 0) (dg3 b 0)) 3) (Nat.mul (nat_lit 3)
    (Nat.add (Nat.mod (Nat.add (dg3 a 1) (dg3 b 1)) 3) (Nat.mul (nat_lit 3)
      (Nat.add (Nat.mod (Nat.add (dg3 a 2) (dg3 b 2)) 3) (Nat.mul (nat_lit 3)
        (Nat.add (Nat.mod (Nat.add (dg3 a 3) (dg3 b 3)) 3) (Nat.mul (nat_lit 3)
          (Nat.mod (Nat.add (dg3 a 4) (dg3 b 4)) 3))))))))

@[expose] noncomputable def pw3 (M : List Nat) (i k : Nat) : Nat :=
  nIf(Nat.beq i 0, k, nIf(Nat.beq i 1, act5 M k, act5 M (act5 M k)))

@[expose] noncomputable def nact (M1 M2 : List Nat) (i j k : Nat) : Nat := pw3 M1 i (pw3 M2 j k)

@[expose] noncomputable def wq (M2 : List Nat) (r2 j : Nat) : Nat :=
  nIf(Nat.beq j 0, 0, nIf(Nat.beq j 1, r2, add5 (act5 M2 r2) r2))

@[expose] noncomputable def rdC (M1 M2 : List Nat) (c k : Nat) : Nat :=
  Nat.add (add5 (Nat.mod c 243) (nact M1 M2 (Nat.mod (Nat.div c 243) 3) (Nat.div c 729) k))
    (Nat.mul 243 (Nat.div c 243))

@[expose] noncomputable def rq1C (M1 M2 : List Nat) (r1 r2 c : Nat) : Nat :=
  strictN (add5 (Nat.mod c 243) (pw3 M1 (Nat.mod (Nat.div c 243) 3) (wq M2 r2 (Nat.div c 729))))
    fun v => nIf(Nat.beq (Nat.mod (Nat.div c 243) 3) 2,
      Nat.add (add5 v r1) (Nat.mul 729 (Nat.div c 729)),
      Nat.add v (Nat.mul 243 (Nat.add (Nat.div c 243) 1)))

@[expose] noncomputable def rq2C (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.div c 729) 2, Nat.sub c 1458, Nat.add c 729)

@[expose] noncomputable def pq1 (M1 M2 : List Nat) (r1 r2 i c : Nat) : Nat :=
  nIf(Nat.beq i 0, c, nIf(Nat.beq i 1, rq1C M1 M2 r1 r2 c,
    strictN (rq1C M1 M2 r1 r2 c) (rq1C M1 M2 r1 r2)))

@[expose] noncomputable def pq2 (j c : Nat) : Nat :=
  nIf(Nat.beq j 0, c, nIf(Nat.beq j 1, rq2C c, rq2C (rq2C c)))

@[expose] noncomputable def mulC (M1 M2 : List Nat) (r1 r2 a b : Nat) : Nat :=
  strictN (rdC M1 M2 a (Nat.mod b 243)) fun x =>
  strictN (pq1 M1 M2 r1 r2 (Nat.mod (Nat.div b 243) 3) x) fun y => pq2 (Nat.div b 729) y

@[expose] noncomputable def cubeC (M1 M2 : List Nat) (r1 r2 c : Nat) : Nat :=
  strictN (mulC M1 M2 r1 r2 c c) fun x => mulC M1 M2 r1 r2 x c

@[expose] noncomputable def distOK (M1 M2 : List Nat) : Bool :=
  allN 9 fun u => allN 9 fun u' => bIf(Nat.beq u u', true,
    bIf(allN 5 fun t => Nat.beq (nact M1 M2 (Nat.mod u 3) (Nat.div u 3) (Nat.pow 3 t))
      (nact M1 M2 (Nat.mod u' 3) (Nat.div u' 3) (Nat.pow 3 t)), false, true))

@[expose] noncomputable def repC (M1 M2 : List Nat) (r1 r2 : Nat) (lc : List Nat) (r : Nat) : Nat :=
  nIf(Nat.blt r 12, nthN lc r,
    mulC M1 M2 r1 r2 (nthN lc (Nat.sub r 12)) (nthN lc (Nat.sub r 12)))

@[expose] noncomputable def fusAt (M1 M2 : List Nat) (r1 r2 : Nat) (lc : List Nat) (c e : Nat) :
    Bool :=
  bIf(Nat.blt c 243, true, bIf(Nat.beq (cubeC M1 M2 r1 r2 c) 0,
    bAnd(Nat.blt (Nat.div e 243) 24, Nat.beq
      (mulC M1 M2 r1 r2 (mulC M1 M2 r1 r2 (Nat.mod e 243) c) (dbl5 (Nat.mod e 243)))
      (repC M1 M2 r1 r2 lc (Nat.div e 243))), true))

@[expose] noncomputable def allIx (f : Nat → Nat → Bool) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih s => bAnd(f s e, strictB (Nat.succ s) ih)) l

@[expose] noncomputable def fusOK (M1 M2 : List Nat) (r1 r2 : Nat) (lc fb : List Nat) : Bool :=
  bAnd(allN 12 fun j => Nat.blt (nthN lc j) 2187, bAnd(Nat.beq fb.length 2187,
    allIx (fusAt M1 M2 r1 r2 lc) fb 0))

@[expose] noncomputable def mdlP (n w : Nat) (D : List Nat) (Q1 Q2 c : Nat) : Nat :=
  ePg n w D (Nat.mod c 243) (mulD n w Q1 (Nat.mod (Nat.div c 243) 3)
    (mulD n w Q2 (Nat.div c 729) (pidn n w)))

@[expose] noncomputable def relOK (n w : Nat) (D : List Nat) (Q0 Q1 Q2 : Nat) (qr : List Nat) : Bool :=
  bAnd(Nat.beq Q0 (ePg n w D (nthN qr 0) (pidn n w)),
    bAnd(Nat.beq (pcomp n w (mask w) Q1 (pcomp n w (mask w) Q1 Q1)) (ePg n w D (nthN qr 1) (pidn n w)),
      bAnd(Nat.beq (pcomp n w (mask w) Q2 (pcomp n w (mask w) Q2 Q2)) (pidn n w),
        Nat.beq (pcomp n w (mask w) Q2 Q1) (ePg n w D (nthN qr 2) (pcomp n w (mask w) Q1 Q2)))))

@[expose] noncomputable def trOK (n w : Nat) (LR TRI : Nat → Nat) (BP : Nat) (D : List Nat)
    (Q1 Q2 Y : Nat) (lc H z : List Nat) : Bool :=
  allN 12 fun j => strictB (nthN H j) fun h => bAnd(inPK n w LR TRI BP h,
    strictB (pcomp n w (mask w) h (mdlP n w D Q1 Q2 (nthN lc j))) fun hR =>
      bIf(Nat.beq (nthN z j) 0, Nat.beq hR (pcomp n w (mask w) Y h),
        Nat.beq hR (ePg n w D (Nat.sub (nthN z j) 243) h)))

end CFSG.KS.QMdlK

end
