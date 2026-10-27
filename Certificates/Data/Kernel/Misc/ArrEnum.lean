module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.ArrEnum

open CFSG.KC.Enum (pg pcomp pidn permOK)
open CFSG.KS (mask pinvS)
open CFSG.KC.LQT.P (allN)

@[expose] noncomputable def permB (n w p : Nat) : Bool :=
  permOK n w (mask w) (Nat.mul n w) p (pinvS n w (mask w) p)

@[expose] noncomputable def keyK (n w : Nat) (ps : List Nat) (p : Nat) : Nat :=
  List.foldr (fun x acc => Nat.add (pg w (mask w) p x) (Nat.mul n acc)) (nat_lit 0) ps

@[expose] noncomputable def pointK (n w ngen N : Nat) (G PT : Nat → Nat) (E : Nat → Nat → Nat)
    (PAR LAB : Nat → Nat) (i : Nat) : Bool :=
  permB n w (PT i) &&
    allN ngen (fun k => Nat.blt (E i k) N &&
      Nat.beq (PT (E i k)) (pcomp n w (mask w) (G k) (PT i))) &&
    (i == 0 || (Nat.blt (PAR i) i && Nat.blt (LAB i) ngen &&
      Nat.beq (PT i) (pcomp n w (mask w) (G (LAB i)) (PT (PAR i)))))

@[expose] noncomputable def pointsK (n w ngen N : Nat) (G PT : Nat → Nat) (E : Nat → Nat → Nat)
    (PAR LAB : Nat → Nat) (lo cnt : Nat) : Bool :=
  allN cnt fun t => pointK n w ngen N G PT E PAR LAB (Nat.add lo t)

@[expose] noncomputable def keysK (n w : Nat) (ps : List Nat) (PT : Nat → Nat) (lo cnt : Nat) :
    Bool :=
  allN cnt fun t => allN (Nat.add lo t) fun j =>
    !(Nat.beq (keyK n w ps (PT (Nat.add lo t))) (keyK n w ps (PT j)))

@[expose] noncomputable def packL (w : Nat) (l : List Nat) : Nat × Bool :=
  List.rec (motive := fun _ => Nat × Bool) (nat_lit 0, true)
    (fun x _ ih => (Nat.lor x (Nat.shiftLeft ih.1 w),
      ih.2 && Nat.blt x (Nat.shiftLeft (nat_lit 1) w))) l

@[expose] noncomputable def arrBind (a : Array Nat) (n w P : Nat) : Bool :=
  Nat.beq a.toList.length n && (packL w a.toList).2 && Nat.beq (packL w a.toList).1 P

@[expose] noncomputable def fixK (n w p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (Nat.beq (pg w (mask w) p i) i))) n

@[expose] noncomputable def memK (N : Nat) (PT : Nat → Nat) (p : Nat) : Bool :=
  CFSG.KC.LQT.P.anyN N fun i => Nat.beq p (PT i)

@[expose] noncomputable def pointA (n w ngen N : Nat) (ACT : Nat → Nat → Nat) (PT : Nat → Nat)
    (E : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (i : Nat) : Bool :=
  permB n w (PT i) &&
    allN ngen (fun k => Nat.blt (E i k) N && Nat.beq (PT (E i k)) (ACT k (PT i))) &&
    (i == 0 || (Nat.blt (PAR i) i && Nat.blt (LAB i) ngen &&
      Nat.beq (PT i) (ACT (LAB i) (PT (PAR i)))))

@[expose] noncomputable def pointsA (n w ngen N : Nat) (ACT : Nat → Nat → Nat) (PT : Nat → Nat)
    (E : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (lo cnt : Nat) : Bool :=
  allN cnt fun t => pointA n w ngen N ACT PT E PAR LAB (Nat.add lo t)

@[expose] noncomputable def conjAct (n w : Nat) (G : Nat → Nat) (k p : Nat) : Nat :=
  pcomp n w (mask w) (G k) (pcomp n w (mask w) p (pinvS n w (mask w) (G k)))

@[expose] noncomputable def headK (n w ngen N : Nat) (G PT : Nat → Nat) : Bool :=
  allN ngen (fun k => permB n w (G k)) && Nat.blt 0 N && Nat.beq (PT 0) (pidn n w)

end CFSG.KC.Misc.ArrEnum

end
