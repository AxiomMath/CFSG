module

public import Certificates.Data.Kernel.Ivk8Norm
public import Certificates.Data.Kernel.YoshQ.TabN

public section

namespace CFSG.KS.Ivk8NormP

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KC.Enum CFSG.KS.PK

@[expose] noncomputable def cmpF (n w a b : Nat) : Nat := pcomp n w (mask w) a b

@[expose] noncomputable def powN (n w y : Nat) : Nat → Nat → Nat
  | 0, z => z
  | k + 1, z => powN n w y k (cmpF n w y z)

@[expose] noncomputable def powsN (n w y : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, z => z :: powsN n w y k (cmpF n w y z)

@[expose] noncomputable def conjF (n w : Nat) (h : Nat × Nat) (y : Nat) : Nat :=
  cmpF n w h.1 (cmpF n w y h.2)

@[expose] def notInN (z : Nat) (ps : List Nat) : Bool := ps.all fun q => !Nat.beq z q

@[expose] noncomputable def movesN (n w : Nat) (hs : List (Nat × Nat)) (y : Nat) (ps : List Nat) :
    Bool :=
  hs.any fun h => notInN (conjF n w h y) ps

@[expose] noncomputable def okP (n w p : Nat) (hs : List (Nat × Nat)) (y : Nat) : Bool :=
  !Nat.beq (powN n w y p (pidn n w)) (pidn n w) || Nat.beq y (pidn n w) ||
    movesN n w hs y (powsN n w y (p - 1) (cmpF n w y (pidn n w)))

@[expose] noncomputable def chkP (n w p : Nat) (hs : List (Nat × Nat)) (L : List Nat) : Bool :=
  L.all (okP n w p hs)

@[expose] def subprodsV {n : Nat} : List (VP n) → List (VP n)
  | [] => [oneV n]
  | s :: S => subprodsV S ++ (subprodsV S).map (mulV s)

@[expose] def invoV {n : Nat} (x : VP n) : Bool := !difV (mulV x x) (oneV n)

@[expose] def commV {n : Nat} (x y : VP n) : Bool := !difV (mulV x y) (mulV y x)

@[expose] noncomputable def resOK (w O k X : Nat) (σ : VP k) : Bool :=
  (List.range k).all fun i =>
    Nat.beq (pg w (mask w) X (pg w (mask w) O i)) (pg w (mask w) O (fd (wd k) σ.1.1 i))

@[expose] noncomputable def sortedOK (w O k n : Nat) : Bool :=
  (List.range k).all fun i =>
    Nat.blt (pg w (mask w) O i) n &&
      (i + 1 == k || Nat.blt (pg w (mask w) O i) (pg w (mask w) O (i + 1)))

end CFSG.KS.Ivk8NormP

end
