module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.U62Q

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def wK (G : Nat → Nat) (u : List (Fin 3)) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 693 10)
    (fun x _ ih => pcomp 693 10 (mask 10) (G x.val) ih) u

@[expose] noncomputable def dg (c : Nat) (x : Fin 3) : Nat :=
  List.getD [c / 9 % 3, c / 3 % 3, c % 3] x.val 0

@[expose] noncomputable def eK (c : Nat) (u : List (Fin 3)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => dg c x + ih) u

@[expose] noncomputable def orthK (c : Nat) (u : List (Fin 3)) : Bool :=
  Nat.beq (eK c u % 3) 0

@[expose] noncomputable def cubeBad (G : Nat → Nat) (u : List (Fin 3)) : Bool :=
  strictB (wK G u) fun p =>
    !Nat.beq (pcomp 693 10 (mask 10) p (pcomp 693 10 (mask 10) p p)) (pidn 693 10)

@[expose] noncomputable def commBad (G : Nat → Nat) (a b : List (Fin 3)) : Bool :=
  strictB (wK G a) fun p => strictB (wK G b) fun q =>
    !Nat.beq (pcomp 693 10 (mask 10) p q) (pcomp 693 10 (mask 10) q p)

@[expose] def cubeW : List (List (Fin 3)) :=
  [[1, 0], [2, 0], [2, 1, 1, 0], [2, 1, 0], [2, 0, 0], [1, 0, 0]]

@[expose] def commW : List (List (Fin 3) × List (Fin 3)) :=
  [([1], [0, 1, 0, 0])]

@[expose] noncomputable def witK (G : Nat → Nat) : Bool :=
  cubeW.all (cubeBad G) && commW.all fun e => commBad G e.1 e.2

@[expose] noncomputable def coverK : Bool :=
  allN 27 fun c => cubeW.any (orthK c) || commW.any fun e => orthK c e.1 && orthK c e.2

end CFSG.KC.U62Q

end
