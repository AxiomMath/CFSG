module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.IrrK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def involP (n w x : Nat) : Bool :=
  bAnd(Nat.beq (pcomp n w (mask w) x x) (pidn n w), bIf(Nat.beq x (pidn n w), false, true))

@[expose] noncomputable def commP (n w x y : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) x y) (pcomp n w (mask w) y x)

@[expose] def memP (L : List Nat) (b : Nat) : Bool := L.any fun y => Nat.beq y b

@[expose] noncomputable def witOneP (n w : Nat) (px : List Nat) (x : Nat) : Bool :=
  px.any fun b₁ => !Nat.beq b₁ x && px.any fun b₂ =>
    commP n w b₂ b₁ && !memP [x, b₁, pcomp n w (mask w) x b₁] b₂

@[expose] noncomputable def witTwoP (n w : Nat) (px : List Nat) (x y : Nat) : Bool :=
  px.any fun b => commP n w b y && !memP [x, y, pcomp n w (mask w) x y] b

@[expose] noncomputable def rowP (n w : Nat) (invs px : List Nat) (x : Nat) : Bool :=
  witOneP n w px x && invs.all fun y => !commP n w x y || Nat.beq x y || witTwoP n w px x y

@[expose] noncomputable def irrP (n w : Nat) (sift : Nat → Bool) (E X : List Nat) : Bool :=
  (E.filter (involP n w)).all fun x =>
    rowP n w (E.filter (involP n w))
      (((E ++ X).filter fun b => involP n w b && sift b).filter fun b => commP n w b x) x

@[expose] noncomputable def candP (n w : Nat) (E X : List Nat) : Bool :=
  (E ++ X).all fun b => canonK n w (mask w) (n * w) b &&
    (!involP n w b || invEqK n w (mask w) (n * w) b b)

end CFSG.KC.IrrK

end
