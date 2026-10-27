module

public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.Spor.Prim

public noncomputable section

namespace CFSG.KC.LocalComp.ThreeWP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

variable (n w : Nat)

@[expose] noncomputable def wordP (F : Int → Nat) : List Int → Nat
  | [] => pidn n w
  | z :: zs => strictN (wordP F zs) fun t => pcomp n w (mask w) (F z) t

@[expose] noncomputable def conjP (g gi x : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) g x) gi

@[expose] noncomputable def commP (x y : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) x y) (pcomp n w (mask w) y x)

@[expose] noncomputable def rf (R t : Nat) : Nat := pg 16 65535 R t

@[expose] noncomputable def headWP (E : Nat → Nat) (m Q Y nc : Nat) : Bool :=
  bAnd(Nat.blt 0 m, bAnd(Nat.beq (E 0) Q,
  bAnd(canonK n w (mask w) (Nat.mul n w) Q, bAnd(canonK n w (mask w) (Nat.mul n w) Y,
  bAnd(Nat.beq (ppow n w (mask w) (pidn n w) Y 3) (pidn n w),
  bAnd(bIf(Nat.beq Y (pidn n w), false, true),
    bAnd(Nat.blt nc m, bIf(commP n w Y (E nc), false, true))))))))

@[expose] noncomputable def rowWP (G GI : Nat → Nat) (k : Nat) (E R : Nat → Nat) (m j : Nat) :
    Bool :=
  bAnd(allN k (fun l =>
    bAnd(strictB (rf (R j) (Nat.add 2 (Nat.mul 2 l))) fun a =>
        bAnd(Nat.blt a m, Nat.beq (E a) (conjP n w (G l) (GI l) (E j))),
      strictB (rf (R j) (Nat.add 3 (Nat.mul 2 l))) fun b =>
        bAnd(Nat.blt b m, Nat.beq (E b) (conjP n w (GI l) (G l) (E j))))),
    bIf(Nat.beq j 0, true,
      strictB (rf (R j) 0) fun p => strictB (rf (R j) 1) fun l =>
        bAnd(Nat.blt p j, bAnd(Nat.blt l k, Nat.beq (E j) (conjP n w (G l) (GI l) (E p))))))

@[expose] noncomputable def commWP (E : Nat → Nat) (i : Nat) : Bool :=
  allN i fun j => commP n w (E i) (E j)

end CFSG.KC.LocalComp.ThreeWP

end
