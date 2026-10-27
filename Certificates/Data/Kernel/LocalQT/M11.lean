module

public import Certificates.Data.Kernel.LocalQT.Small
public import Certificates.Data.Kernel.LocalQT.Word

public section

namespace CFSG.KC.LQT.M

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W

@[expose] noncomputable def okIx (k j : Nat) : Bool := Nat.ble k j

@[expose] noncomputable def getW (W : List (List Nat)) (j : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Bool.rec (motive := fun _ => List Nat) (ih (Nat.sub i 1)) x (Nat.beq i 0)) W j

@[expose] noncomputable def allMa (R1 R2 R3 R4 : List Nat) (f : Nat → Bool) (a : Nat) : Bool :=
  letB (genAt 11 R1 a) fun p1 =>
  allN 11 fun b => impB (okIx 1 b)
    (letB (mul 11 p1 (genAt 11 R2 b)) fun p2 =>
    allN 11 fun c => impB (okIx 2 c)
      (letB (mul 11 p2 (genAt 11 R3 c)) fun p3 =>
      allN 11 fun d => impB (okIx 3 d) (f (mul 11 p3 (genAt 11 R4 d)))))

@[expose] noncomputable def allM (R1 R2 R3 R4 : List Nat) (f : Nat → Bool) : Bool :=
  allN 11 (allMa R1 R2 R3 R4 f)

@[expose] noncomputable def siftM (R1 R2 R3 R4 : List Nat) (x : Nat) : Bool :=
  letB (mul 11 (inv 11 (genAt 11 R1 (img x 0))) x) fun h1 =>
  letB (mul 11 (inv 11 (genAt 11 R2 (img h1 1))) h1) fun h2 =>
  letB (mul 11 (inv 11 (genAt 11 R3 (img h2 2))) h2) fun h3 =>
    Nat.beq (mul 11 (inv 11 (genAt 11 R4 (img h3 3))) h3) (one 11)

@[expose] noncomputable def repsOK (G : List Nat) (k : Nat) (R : List Nat) (W : List (List Nat)) :
    Bool :=
  allN 11 fun j => impB (okIx k j) (letB (genAt 11 R j) fun r =>
    andB (permK 11 r) (andB (allN k fun i => Nat.beq (img r i) i)
      (andB (Nat.beq (img r k) j) (Nat.beq r (evalWK 11 G (getW W j))))))

@[expose] noncomputable def grpM (CA CB : Nat) (R1 R2 R3 R4 : List Nat)
    (W1 W2 W3 W4 : List (List Nat)) : Bool :=
  andB (repsOK [CA, CB] 0 R1 W1) (andB (repsOK [CA, CB] 1 R2 W2) (andB (repsOK [CA, CB] 2 R3 W3)
  (andB (repsOK [CA, CB] 3 R4 W4) (andB (permK 11 CA) (andB (permK 11 CB)
  (andB (siftM R1 R2 R3 R4 (one 11))
    (allM R1 R2 R3 R4 fun s =>
      andB (siftM R1 R2 R3 R4 (mul 11 s CA)) (siftM R1 R2 R3 R4 (mul 11 s CB)))))))))

@[expose] noncomputable def invsL (l : List Nat) : List Nat :=
  filtL l fun x => andB (notB (Nat.beq x (one 11))) (Nat.beq (mul 11 x x) (one 11))

@[expose] noncomputable def normK (SA SB : Nat) (LP : List Nat) (x : Nat) : Bool :=
  impB (memL (conj 11 x SA) LP) (impB (memL (conj 11 x SB) LP) (memL x LP))

@[expose] noncomputable def centK (LP : List Nat) (x : Nat) : Bool :=
  allL (invsL LP) fun t => allL (invsL LP) fun s =>
    impB (comm 11 x t) (impB (comm 11 x s) (impB (notB (Nat.beq t s)) (impB (comm 11 t s)
      (orB (Nat.beq x (one 11)) (orB (Nat.beq x t) (orB (Nat.beq x s) (Nat.beq x (mul 11 t s))))))))

@[expose] noncomputable def c4154 (R1 R2 R3 R4 LP : List Nat) (SA SB : Nat) : Bool :=
  allM R1 R2 R3 R4 fun x => andB (normK SA SB LP x) (centK LP x)

@[expose] noncomputable def fstM (w : Nat) : Nat := Nat.land w (Nat.sub (Nat.shiftLeft 1 55) 1)

@[expose] noncomputable def sndM (w : Nat) : Nat := Nat.shiftRight w 55

@[expose] noncomputable def f4144 (R1 R2 R3 R4 : List Nat) (CA : Nat) (LT WI : List Nat)
    (x : Nat) : Bool :=
  andB (iffB (andB (comm 11 x CA) (Nat.beq (pow 11 x 3) (one 11))) (memL x LT))
  (andB (impB (comm 11 x CA) (impB (allL LT fun t => comm 11 t x)
    (orB (Nat.beq x (one 11)) (Nat.beq x CA))))
  (andB (impB (allL LT fun t => comm 11 x t) (orB (Nat.beq x (one 11)) (Nat.beq x CA)))
    (impB (notB (Nat.beq x (one 11))) (impB (Nat.beq (mul 11 x x) (one 11))
      (anyL WI fun w => andB (Nat.beq (fstM w) x) (andB (siftM R1 R2 R3 R4 (sndM w))
        (Nat.beq (mul 11 (sndM w) CA) (mul 11 x (sndM w)))))))))

@[expose] noncomputable def c4144 (R1 R2 R3 R4 : List Nat) (CA : Nat) (LT WI : List Nat) : Bool :=
  allM R1 R2 R3 R4 (f4144 R1 R2 R3 R4 CA LT WI)

@[expose] noncomputable def orderK (x m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r ih p => Bool.rec (motive := fun _ => Bool)
      (andB (notB (Nat.beq p (one 11))) (ih (mul 11 p x))) (Nat.beq p (one 11)) (Nat.beq r 0))
    m x

@[expose] noncomputable def wordK (x y : Nat) : Nat :=
  CFSG.KC.Loop.strictN (mul 11 y y) fun y2 =>
    mul 11 (mul 11 (mul 11 x y) (mul 11 x y2)) (mul 11 x (mul 11 y y2))

@[expose] noncomputable def cntY (x : Nat) (LF : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun y _ ih => Nat.add (Bool.rec (motive := fun _ => Nat) 0 1
      (andB (orderK (mul 11 x y) 11) (orderK (wordK x y) 3))) ih) LF

@[expose] noncomputable def cntL (LX LF : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add (cntY x LF) ih) LX

@[expose] noncomputable def cntOK (LX LF : List Nat) (N : Nat) : Bool := Nat.beq (cntL LX LF) N

@[expose] noncomputable def rowT (x : Nat) (LI : List Nat) : Bool :=
  allL LI fun y => orB (notB (comm 11 x y)) (allL LI fun z =>
    orB (notB (andB (comm 11 x z) (comm 11 y z)))
      (orB (Nat.beq x z) (orB (Nat.beq x y) (orB (Nat.beq x (mul 11 y z)) (Nat.beq y z)))))

@[expose] noncomputable def tripL (LX LI : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (rowT x LI) ih) LX

@[expose] noncomputable def c4135 (R1 R2 R3 R4 : List Nat) (CA : Nat) (LI LF WI LG : List Nat) :
    Bool :=
  andB (allL LI (siftM R1 R2 R3 R4)) (andB (allL LF (siftM R1 R2 R3 R4))
  (andB (distinctL LI) (andB (distinctL LF)
  (andB (allL LI fun x => anyL WI fun w => andB (Nat.beq (fstM w) x)
      (andB (siftM R1 R2 R3 R4 (sndM w)) (Nat.beq (conj 11 (sndM w) CA) x)))
    (allL LG fun g => andB (siftM R1 R2 R3 R4 g) (orderK g 2))))))

@[expose] noncomputable def m4135 (R1 R2 R3 R4 LI LF : List Nat) (a : Nat) : Bool :=
  allMa R1 R2 R3 R4 (fun x => andB (iffB (orderK x 2) (memL x LI))
    (iffB (orderK x 4) (memL x LF))) a

@[expose] noncomputable def pwM (x e nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (one 11)
    (fun k acc => CFSG.KC.Loop.strictN (mul 11 acc acc) fun a2 =>
      Bool.rec (motive := fun _ => Nat) a2 (mul 11 a2 x)
        (Nat.blt 0 (Nat.land e (Nat.shiftLeft 1 (Nat.sub (Nat.sub nb 1) k))))) nb

@[expose] noncomputable def oddK (x : Nat) : Bool :=
  andB (notB (Nat.beq x (one 11))) (Nat.beq (pwM x 495 9) (one 11))

@[expose] noncomputable def invoM (x : Nat) : Bool :=
  andB (notB (Nat.beq x (one 11))) (Nat.beq (mul 11 x x) (one 11))

@[expose] noncomputable def ord4M (x : Nat) : Bool :=
  letB (mul 11 x x) fun x2 => andB (Nat.beq (mul 11 x2 x2) (one 11)) (notB (Nat.beq x2 (one 11)))

@[expose] noncomputable def cntM (R1 R2 R3 R4 : List Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun a acc => Nat.add acc
    (CFSG.KC.Loop.strictN (genAt 11 R1 a) fun p1 =>
    Nat.rec (motive := fun _ => Nat) 0 (fun b acc2 => Nat.add acc2
      (Bool.rec (motive := fun _ => Nat) 0
        (CFSG.KC.Loop.strictN (mul 11 p1 (genAt 11 R2 b)) fun p2 =>
        Nat.rec (motive := fun _ => Nat) 0 (fun c acc3 => Nat.add acc3
          (Bool.rec (motive := fun _ => Nat) 0
            (CFSG.KC.Loop.strictN (mul 11 p2 (genAt 11 R3 c)) fun p3 =>
            Nat.rec (motive := fun _ => Nat) 0 (fun d acc4 => Nat.add acc4
              (Bool.rec (motive := fun _ => Nat) 0
                (Bool.rec (motive := fun _ => Nat) 0 1 (f (mul 11 p3 (genAt 11 R4 d))))
                (okIx 3 d))) 11)
            (okIx 2 c))) 11)
        (okIx 1 b))) 11)) 11

@[expose] noncomputable def e4054 (CA CB : Nat) (RO : List Nat) (CI : List (List Nat))
    (T0 : Nat) (S0 C0 : List Nat) (x : Nat) : Bool :=
  andB (orB (Nat.beq x (one 11)) (orB (notB (comm 11 x CA)) (notB (comm 11 x CB))))
  (andB (allN (lenL RO) fun i => impB (comm 11 x (getK RO i))
    (andB (notB (ord4M x)) (impB (invoM x) (memL x (getW CI i)))))
  (andB (impB (Nat.beq (mul 11 x x) T0) (memL x S0)) (impB (comm 11 x T0) (memL x C0))))

@[expose] noncomputable def c4054 (R1 R2 R3 R4 : List Nat) (RO : List Nat) (CI : List (List Nat))
    (T0 : Nat) (S0 C0 : List Nat) : Bool := allBs
  [Nat.beq (cntM R1 R2 R3 R4 fun _ => true) 7920,
   allL RO fun r => andB (siftM R1 R2 R3 R4 r) (oddK r),
   allN (lenL RO) (fun i => allN (lenL RO) fun j => impB (Nat.blt i j)
     (allM R1 R2 R3 R4 fun g => notB (Nat.beq (conj 11 g (getK RO i)) (getK RO j)))),
   Nat.beq (cntM R1 R2 R3 R4 oddK)
     (List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.add
       (Nat.div 7920 (cntM R1 R2 R3 R4 fun x => comm 11 x r)) ih) RO),
   Nat.beq (lenL RO) (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) CI),
   List.rec (motive := fun _ => Bool) true (fun l _ ih => andB (allL l fun t => allL l fun s =>
     impB (notB (Nat.beq t s)) (notB (comm 11 t s))) ih) CI,
   siftM R1 R2 R3 R4 T0, invoM T0,
   Nat.beq (cntM R1 R2 R3 R4 invoM) (Nat.div 7920 (cntM R1 R2 R3 R4 fun x => comm 11 x T0)),
   allL S0 (fun y => andB (siftM R1 R2 R3 R4 y) (Nat.beq (mul 11 y y) T0)),
   notB (Nat.beq (lenL S0) 0), distinctL (one 11 :: T0 :: S0), Nat.ble 3 (lenL S0),
   allL S0 (fun y => allL S0 fun y' => letB (mul 11 y y') fun p =>
     orB (Nat.beq p (one 11)) (orB (Nat.beq p T0) (Nat.beq (mul 11 p p) T0))),
   allL C0 (fun c => andB (siftM R1 R2 R3 R4 c) (comm 11 c T0)),
   allL C0 (fun c => orB (orB (Nat.beq c (one 11)) (orB (Nat.beq c T0) (Nat.beq (mul 11 c c) T0)))
     (anyL C0 fun w => notB (Nat.beq (pwM (mul 11 (inv 11 c) (mul 11 (mul 11 w c) (inv 11 w)))
       16 5) (one 11))))]

@[expose] noncomputable def m4054 (R1 R2 R3 R4 : List Nat) (CA CB : Nat) (RO : List Nat)
    (CI : List (List Nat)) (T0 : Nat) (S0 C0 : List Nat) (a : Nat) : Bool :=
  allMa R1 R2 R3 R4 (e4054 CA CB RO CI T0 S0 C0) a

end CFSG.KC.LQT.M

end
