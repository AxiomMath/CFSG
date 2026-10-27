module

public import CFSG.Milestones.ASVolI.F48.Small.AutChartInputs
public import Certificates.Data.Kernel.F48Small.Sp43c
public import Mathlib

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L CFSG.ASVolI

@[expose] def autcSplit (c : Char) (l : List Char) : List Char → List (List Char) :=
  List.rec (motive := fun _ => List Char → List (List Char)) (fun acc => [acc.reverse])
    (fun a _ ih acc => Bool.rec (motive := fun _ => List (List Char)) (ih (a :: acc))
      (acc.reverse :: ih []) (a == c)) l

@[expose] def autcWords (cs : List Char) : List (List (Fin 5 × Bool)) :=
  (autcSplit ',' cs []).map fun l => l.map burnsideF48s_autc_letter

@[expose] def autcLetOK (gl gli : List (List ℕ)) : Bool :=
  Nat.ble 5 gl.length && Nat.ble 5 gli.length &&
    (gl ++ gli).all fun l => l.length == 45 && l.all fun e => Nat.blt e 64

@[expose] def autcHead (W : List (List (Fin 5 × Bool))) (idx : List (Fin 5)) (n : ℕ) : Bool :=
  decide (W.length = n) && decide ([] ∈ W) && W.all fun w => w.all fun l => decide (l.1 ∈ idx)

@[expose] noncomputable def autcInfK (L1 : List Nat) (T2 TB : NT) : Bool :=
  allA L1 fun x => orB (notB (memT T2 x)) (memT TB x)

end CFSG.KC.F48S
