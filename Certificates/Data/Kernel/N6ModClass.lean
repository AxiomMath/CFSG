module

public import CFSG.CGT.T75JM.N6Class
public import Mathlib

public section

namespace CFSG.KernelN6

open CFSG.CGT.T75JM

@[expose] def transvC : Cols := ⟨1, 2, 4, 9⟩

@[expose] def repC (r : ℕ) : Cols := if r = 0 then modelX else transvC

@[expose] def cjC (P Pi A : Cols) : Cols := compC (compC Pi A) P

@[expose] def eqC (a b : Cols) : Bool :=
  Nat.beq a.c0 b.c0 && Nat.beq a.c1 b.c1 && Nat.beq a.c2 b.c2 && Nat.beq a.c3 b.c3

@[expose] def smallB (a : Cols) : Bool :=
  Nat.blt a.c0 16 && Nat.blt a.c1 16 && Nat.blt a.c2 16 && Nat.blt a.c3 16

@[expose] def relCB (X Y : Cols) : Bool :=
  eqC (compC X X) idC && !eqC X idC && eqC (powC Y 4) idC && eqC (powC (compC X Y) 5) idC &&
    eqC (powC (compC X (compC Y Y)) 5) idC

@[expose] def equivB (X Y Q Qi : Cols) : Bool :=
  smallB Q && smallB Qi && eqC (compC Qi Q) idC && eqC (compC Q Qi) idC &&
    eqC (compC X Q) (compC Q modelX) && eqC (compC Y Q) (compC Q modelY)

@[expose] def isInvB (m : ℕ) : Bool :=
  eqC (compC (unpackC m) (unpackC m)) idC && !eqC (unpackC m) idC

@[expose] def relB (r n : ℕ) : Bool := relCB (repC r) (unpackC n)

@[expose] def invRecOK (e : ℕ) : Bool :=
  eqC (compC (unpackC (e / 65536 ^ 2 % 65536)) (unpackC (e / 65536 % 65536))) idC &&
    eqC (compC (unpackC (e / 65536 % 65536)) (unpackC (e / 65536 ^ 2 % 65536))) idC &&
    eqC (cjC (unpackC (e / 65536 % 65536)) (unpackC (e / 65536 ^ 2 % 65536)) (unpackC (e % 65536)))
      (repC (e / 65536 ^ 3))

@[expose] def relRecOK (e : ℕ) : Bool :=
  equivB modelX
    (if e / 65536 ^ 3 = 0 then unpackC (e % 65536) else evalC modelX (unpackC (e % 65536)) twistWord)
    (unpackC (e / 65536 % 65536)) (unpackC (e / 65536 ^ 2 % 65536))

@[expose] def eqNL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && eqNL s t
  | _, _ => false

@[expose] def invAll (L : List ℕ) : Bool :=
  eqNL ((List.range' 0 65536).filter isInvB) (L.map (· % 65536)) && L.all invRecOK

@[expose] def relAll (r : ℕ) (L : List ℕ) : Bool :=
  eqNL ((List.range' 0 65536).filter (relB r)) (L.map (· % 65536)) && L.all relRecOK

end CFSG.KernelN6
