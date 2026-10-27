module

public import Init

public section

namespace CFSG.KC.FischerE

@[expose] noncomputable def insL (R : List Nat) : Nat → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → Nat → List Nat) (fun _ _ => [])
    (fun t ts ih p v =>
      Bool.rec (motive := fun _ => List Nat) (List.cons t (ih (Nat.sub p 1) v))
        (Bool.rec (motive := fun _ => List Nat) (List.cons t (ih (Nat.sub p 1) (Nat.xor v t)))
          (List.cons v ts) (Nat.beq t 0))
        (Nat.blt 0 (Nat.land v (Nat.shiftLeft 1 p)))) R

@[expose] noncomputable def elimL (p : Nat) (vs : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun R => R)
    (fun v _ ih R => ih (insL R p v)) vs

@[expose] noncomputable def zerosL (d : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun _ ih => List.cons 0 ih) d

@[expose] noncomputable def nzL (R : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun t _ ih => Bool.rec (motive := fun _ => Nat) (Nat.succ ih) ih (Nat.beq t 0)) R

@[expose] noncomputable def wordL (F : Nat → Nat → Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y) (fun j _ ih y => F j (ih y)) w

@[expose] noncomputable def invWordL (G : Nat → Nat → Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun j _ ih x => ih (G j x)) w

end CFSG.KC.FischerE

end
