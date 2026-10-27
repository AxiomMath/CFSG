module

public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.U43Case

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def pp (n w x y : Nat) : Nat := pcomp n w (mask w) x y

@[expose] noncomputable def ppw (n w x a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w) (fun _ acc => pp n w x acc) a

@[expose] noncomputable def ord3P (n w x : Nat) : Bool :=
  andB (Nat.beq (ppw n w x 3) (pidn n w)) (notB (Nat.beq (ppw n w x 1) (pidn n w)))

@[expose] noncomputable def commP (n w a b : Nat) : Bool := Nat.beq (pp n w a b) (pp n w b a)

@[expose] noncomputable def cpP (n w t c : Nat) : Nat := pp n w (pp n w t c) t

@[expose] noncomputable def relFreeP (n w y c c' : Nat) : Bool :=
  (List.range 3).all fun a => (List.range 3).all fun b => (List.range 3).all fun d =>
    (a == 0 && b == 0 && d == 0) ||
      !Nat.beq (pp n w (pp n w (ppw n w y a) (ppw n w c b)) (ppw n w c' d)) (pidn n w)

@[expose] noncomputable def candP (n w t y c : Nat) : Bool :=
  ord3P n w c && commP n w c (cpP n w t c) && commP n w y (cpP n w t c) &&
    relFreeP n w y c (cpP n w t c)

@[expose] noncomputable def kP (n w t c k : Nat) : Bool :=
  (Nat.beq (pp n w k k) (pidn n w) && !Nat.beq k (pidn n w)) && commP n w k (cpP n w t c) &&
    commP n w k (cpP n w t k) && Nat.beq (pp n w (pp n w (pp n w k c) k) c) (pidn n w)

@[expose] noncomputable def solsP (n w t y N : Nat) (Y : Nat → Nat) : List (Nat × Nat) :=
  ((List.range N).filter fun i => candP n w t y (Y i)).flatMap fun i =>
    ((List.range N).filter fun j => kP n w t (Y i) (Y j)).map fun j => (i, j)

@[expose] noncomputable def cent5P (n w t N : Nat) (Y : Nat → Nat) (c k : Nat) : Nat :=
  ((List.range N).filter fun i => commP n w (Y i) c && commP n w (Y i) (cpP n w t c) &&
    commP n w (Y i) k && commP n w (Y i) (cpP n w t k)).length

@[expose] noncomputable def solK (n w t y N : Nat) (Y : Nat → Nat) (nsol : Nat) : Bool :=
  (solsP n w t y N Y).length == nsol &&
    (solsP n w t y N Y).all fun p => cent5P n w t N Y (Y p.1) (Y p.2) == 3

@[expose] noncomputable def coverP (n w NC : Nat) (C : Nat → Nat) (NQ : Nat) (Q W : Nat → Nat)
    (lo len : Nat) : Bool :=
  (List.range len).all fun d => strictB (Nat.add lo d) fun i =>
    !Nat.blt i NC || !ord3P n w (C i) || (Nat.blt (W i) NQ && Nat.beq (Q (W i)) (C i))

end CFSG.KC.U43Case

end
