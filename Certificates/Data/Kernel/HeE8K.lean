module

public import Certificates.Data.Kernel.Spor.Chain

@[expose] public section

namespace CFSG.KC.HeE8K

open CFSG.KC.Enum CFSG.KS

noncomputable def rdK (P q : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (pg 14 (mask 14) P q) (Nat.blt q 8330)

noncomputable def evK (P0 P1 : Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p
    (fun k _ q => Bool.rec (motive := fun _ => Nat) (rdK P1 q) (rdK P0 q) (Nat.beq k 0)) w

def heE8OKF (ev : List Nat → Nat → Nat) : Bool :=
  let w1 : List Nat := [0]
  let w2 : List Nat :=
    [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1]
  let w3 : List Nat :=
    [1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1]
  let fb : List Nat → Bool := fun w => (List.range 5).all fun b => ev w b == b
  let wv : Bool × Bool × Bool → List Nat := fun v =>
    (if v.1 then w1 else []) ++ (if v.2.1 then w2 else []) ++ (if v.2.2 then w3 else [])
  (w1 ++ w2 ++ w3).all (fun k => decide (k < 2)) &&
    fb (w1 ++ w1) && fb (w2 ++ w2) && fb (w3 ++ w3) && fb (w1 ++ w2 ++ w1 ++ w2) &&
    fb (w1 ++ w3 ++ w1 ++ w3) && fb (w2 ++ w3 ++ w2 ++ w3) &&
    decide (([(false, false, false), (false, false, true), (false, true, false),
      (false, true, true), (true, false, false), (true, false, true), (true, true, false),
      (true, true, true)] : List (Bool × Bool × Bool)).map
        (fun v => (List.range 5).map (ev (wv v)))).Nodup

end CFSG.KC.HeE8K
