module

public import Certificates.Data.Kernel.ConjWalk

public section

namespace CFSG.KC.ConjWalk

@[expose] noncomputable def keyL (n : Nat) (ps : List Nat) (C : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.add (ln C a) (Nat.mul n ih)) ps

@[expose] noncomputable def walkLAux (n : Nat) (ps : List Nat) (X0 X0I X1 X1I : Nat)
    (recs : List Nat) : List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Nat → Bool) (fun _ _ _ => true)
    (fun r _ ih s S d => strictB (Nat.shiftRight r 1) fun p =>
      Nat.blt p d &&
      strictB (Bool.rec (motive := fun _ => Nat) (cjP n X1 X1I (topS (popS p s)))
        (cjP n X0 X0I (topS (popS p s))) (Nat.beq (Nat.land r 1) 0)) fun C =>
      strictB (keyL n ps C) fun k =>
      Nat.beq (Nat.land (Nat.shiftRight S k) 1) 0 &&
      strictB (Nat.lor S (Nat.shiftLeft 1 k)) fun S' =>
      strictB (Nat.succ (Nat.sub d p)) fun d' => ih (C :: popS p s) S' d') recs

@[expose] noncomputable def walkKL (n : Nat) (ps : List Nat) (X0 X0I X1 X1I T : Nat)
    (recs : List Nat) : Bool :=
  strictB X0 fun X0 => strictB X0I fun X0I => strictB X1 fun X1 => strictB X1I fun X1I =>
  strictB T fun T => strictB (keyL n ps T) fun k =>
  walkLAux n ps X0 X0I X1 X1I recs [T] (Nat.shiftLeft 1 k) 1

end CFSG.KC.ConjWalk

end
