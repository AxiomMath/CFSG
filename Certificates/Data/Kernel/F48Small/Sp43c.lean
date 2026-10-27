module

public import Certificates.Data.Kernel.F48Small.Pack

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L

@[expose] def decSp43c (i : Nat) : Char :=
  ['a', 'b', 'c', 'p', 'q', 'A', 'B', 'C', 'P', 'Q'].getD i 'a'

@[expose] def letB43c (c : Nat) : Fin 2 × Bool :=
  (if c % 5 = 1 then 1 else 0, Nat.blt c 5)

@[expose] def letS43c (c : Nat) : Fin 2 × Bool :=
  (if c % 5 = 2 then 1 else 0, Nat.blt c 5)

@[expose] def letP43c (c : Nat) : Fin 3 × Bool :=
  (if c % 5 = 1 then 1 else if c % 5 = 3 then 2 else 0, Nat.blt c 5)

@[expose] def letQ43c (c : Nat) : Fin 3 × Bool :=
  (if c % 5 = 1 then 1 else if c % 5 = 4 then 2 else 0, Nat.blt c 5)

@[expose] noncomputable def codesLt10 (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (List.rec (motive := fun _ => Bool) true
      (fun c _ ih' => andB (Nat.blt c 10) ih') w) ih) L

@[expose] noncomputable def nodupT (L : List Nat) : NT → Bool :=
  List.rec (motive := fun _ => NT → Bool) (fun _ => true)
    (fun x _ ih t => andB (notB (memT t x)) (ih (insT t x))) L

@[expose] noncomputable def groupK (N : Nat) (LP GP : List Nat) : Bool :=
  andB (nodupT LP NT.lf) (closedK N (setT LP) LP GP)

end CFSG.KC.F48S
