module

public import Init

public section

namespace CFSG.KC.ConjWalk

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def ln (N q : Nat) : Nat := Nat.land (Nat.shiftRight N (Nat.mul 6 q)) 63

@[expose] noncomputable def pkN (f : Nat → Nat) (k s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih s => Nat.add (f s) (Nat.mul 64 (ih (Nat.succ s)))) k s

@[expose] noncomputable def cjP (n G GI C : Nat) : Nat :=
  pkN (fun p => ln G (ln C (ln GI p))) n 0

@[expose] noncomputable def keyP (a b c C : Nat) : Nat :=
  Nat.add (ln C a) (Nat.mul 64 (Nat.add (ln C b) (Nat.mul 64 (ln C c))))

@[expose] noncomputable def popS (p : Nat) (s : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) s
    (fun _ ih => List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) ih) p

@[expose] noncomputable def topS (s : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ _ => a) s

@[expose] noncomputable def walkAux (n a b c X0 X0I X1 X1I : Nat) (recs : List Nat) :
    List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Nat → Bool) (fun _ _ _ => true)
    (fun r _ ih s S d => strictB (Nat.shiftRight r 1) fun p =>
      Nat.blt p d &&
      strictB (Bool.rec (motive := fun _ => Nat) (cjP n X1 X1I (topS (popS p s)))
        (cjP n X0 X0I (topS (popS p s))) (Nat.beq (Nat.land r 1) 0)) fun C =>
      strictB (keyP a b c C) fun k =>
      Nat.beq (Nat.land (Nat.shiftRight S k) 1) 0 &&
      strictB (Nat.lor S (Nat.shiftLeft 1 k)) fun S' =>
      strictB (Nat.succ (Nat.sub d p)) fun d' => ih (C :: popS p s) S' d') recs

@[expose] noncomputable def walkK (n a b c X0 X0I X1 X1I T : Nat) (recs : List Nat) : Bool :=
  strictB X0 fun X0 => strictB X0I fun X0I => strictB X1 fun X1 => strictB X1I fun X1I =>
  strictB T fun T => strictB (keyP a b c T) fun k =>
  walkAux n a b c X0 X0I X1 X1I recs [T] (Nat.shiftLeft 1 k) 1

end CFSG.KC.ConjWalk

end
