module

public import Certificates.Data.Kernel.LocalQT.M11

public section

namespace CFSG.KC.LQT.X6

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S

@[expose] noncomputable def rank6 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc (Nat.mul
    (Nat.rec (motive := fun _ => Nat) 0 (fun j c => Nat.add c
      (Bool.rec (motive := fun _ => Nat) 0 1
        (andB (Nat.blt i j) (Nat.blt (img x j) (img x i))))) 6)
    (Nat.rec (motive := fun _ => Nat) 1 (fun k f => Nat.mul f (Nat.succ k)) (Nat.sub 5 i)))) 6

@[expose] noncomputable def inM (m x : Nat) : Bool :=
  Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 (rank6 x)))

@[expose] noncomputable def letP (y : Nat) (k : Nat → Nat × List Nat) : Nat × List Nat :=
  Nat.rec (motive := fun _ => Nat × List Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def stepK (G old : List Nat) (st : Nat × List Nat) : Nat × List Nat :=
  List.rec (motive := fun _ => Nat × List Nat → Nat × List Nat) (fun st => st)
    (fun x _ ih st => ih (List.rec (motive := fun _ => Nat × List Nat → Nat × List Nat)
      (fun st => st)
      (fun g _ ih2 st => ih2 (letP (mul 6 x g) fun y =>
        Bool.rec (motive := fun _ => Nat × List Nat)
          (Prod.mk (Nat.lor st.1 (Nat.shiftLeft 1 (rank6 y))) (List.cons y st.2)) st (inM st.1 y)))
      G st)) old st

@[expose] noncomputable def ballK (G : List Nat) (n : Nat) : Nat × List Nat :=
  Nat.rec (motive := fun _ => Nat × List Nat)
    (Prod.mk (Nat.shiftLeft 1 (rank6 (one 6))) [one 6]) (fun _ st => stepK G st.2 st) n

@[expose] noncomputable def closedK (G : List Nat) (B : Nat × List Nat) : Bool :=
  allL B.2 fun x => allL G fun g => inM B.1 (mul 6 x g)

@[expose] noncomputable def c4051 (G0 Ga Gb RP : List Nat) (n0 na nb m k0 ka kb : Nat) : Bool :=
  letB (ballK G0 n0).1 fun M0 => letB (ballK Ga na).1 fun Ma => letB (ballK Gb nb).1 fun Mb => allBs
  [Nat.beq (lenL (ballK G0 n0).2) k0, Nat.beq (lenL (ballK Ga na).2) ka,
   Nat.beq (lenL (ballK Gb nb).2) kb,
   closedK G0 (ballK G0 n0), closedK Ga (ballK Ga na), closedK Gb (ballK Gb nb),
   allP 6 (fun x => impB (even 6 x) (orB (inM Ma x) (orB (inM Mb x)
     (anyL RP fun r => anyL (ballK G0 n0).2 fun d => inM M0 (mul 6 (mul 6 (inv 6 r) (inv 6 d)) x))))),
   allL RP (fun r => letB (ballK (List.append G0 [r]) m).1 fun M =>
     allP 6 fun x => impB (even 6 x) (inM M x)),
   allP 6 (fun t => impB (allL G0 fun g => inM M0 (conj 6 t g))
     (andB (allL Ga fun g => inM Ma (conj 6 t g)) (allL Gb fun g => inM Mb (conj 6 t g))))]

@[expose] noncomputable def keyK (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc (Nat.mul (img x i) (Nat.pow 6 i))) 6

@[expose] noncomputable def lookW (T : List (Nat × List Bool)) (k : Nat) : List Bool :=
  List.rec (motive := fun _ => List Bool) [] (fun p _ ih =>
    Bool.rec (motive := fun _ => List Bool) ih p.2 (Nat.beq p.1 k)) T

@[expose] noncomputable def evK (x y : Nat) (w : List Bool) : Nat :=
  List.rec (motive := fun _ => Nat) (one 6)
    (fun c _ ih => mul 6 (Bool.rec (motive := fun _ => Nat) x y c) ih) w

@[expose] noncomputable def phiK (T : List (Nat × List Bool)) (x y g : Nat) : Nat :=
  evK x y (lookW T (keyK g))

@[expose] noncomputable def powK (x n : Nat) : Nat := pow 6 x n

@[expose] noncomputable def tauK (x q p : Nat) : Nat :=
  ofFn 6 fun j => Bool.rec (motive := fun _ => Nat) (img (powK x j) q) p (Nat.beq j 5)

@[expose] noncomputable def fixPt (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc
    (Bool.rec (motive := fun _ => Nat) 0 i (Nat.beq (img x i) i))) 6

@[expose] noncomputable def conjOK (CA CB x y : Nat) : Bool :=
  letB (Bool.rec (motive := fun _ => Nat) 1 0 (notB (Nat.beq (img x 0) 0))) fun r0 =>
  anyN 5 fun m => letB (tauK x (img (powK x m) r0) (fixPt x)) fun t =>
    andB (permK 6 t) (andB (Nat.beq (conj 6 t CA) x) (Nat.beq (conj 6 t CB) y))

@[expose] noncomputable def relK (R : List (List Bool)) (x y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (Nat.beq (evK x y r) (one 6)) ih) R

@[expose] noncomputable def flatL (l : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun c _ ih => List.append c ih) l

@[expose] noncomputable def c4035 (T : List (Nat × List Bool)) (R : List (List Bool))
    (LA : List Nat) (LXs : List (List Nat)) (LY : List Nat) (CA CB : Nat) : Bool := allBs
  [relK R CA CB,
   allP 6 (fun g => impB (even 6 g) (Nat.beq (phiK T CA CB g) g)),
   allL LA (fun a => andB (permK 6 a) (even 6 a)),
   allP 6 (fun x => impB (andB (even 6 x) (Nat.beq (powK x 5) (one 6))) (memL x (flatL LXs))),
   allP 6 (fun y => impB (andB (even 6 y) (Nat.beq (powK y 3) (one 6))) (memL y LY))]

@[expose] noncomputable def p4035 (T : List (Nat × List Bool)) (R : List (List Bool))
    (LA : List Nat) (LXs : List (List Nat)) (LY : List Nat) (CA CB i : Nat) : Bool :=
  allL (CFSG.KC.LQT.M.getW LXs i) fun x => allL LY fun y => impB (relK R x y)
    (orB (conjOK CA CB x y)
    (orB (anyL LA fun a => andB (notB (Nat.beq a (one 6)))
        (andB (Nat.beq (powK a 5) (one 6)) (Nat.beq (phiK T x y a) a)))
      (anyL LA fun g => notB (Nat.beq (phiK T x y (phiK T x y g)) g))))

end CFSG.KC.LQT.X6

end
