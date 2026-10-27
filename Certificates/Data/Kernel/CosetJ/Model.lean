module

public import Init

public section

namespace CFSG.KC.CosetJ.Model

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def allN (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (p i) ih) n

@[expose] noncomputable def getL (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun h _ ih i => Nat.rec (motive := fun _ => Nat) h (fun j _ => ih j) i) L

@[expose] noncomputable def getLL (G : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List Nat) h (fun j _ => ih j) i) G

@[expose] noncomputable def letterV (G I : List (List Nat)) (l : Nat × Bool) (y : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun g s => Bool.rec (motive := fun _ => Nat) (getL (getLL I g) y) (getL (getLL G g) y) s) l

@[expose] noncomputable def walk (G I : List (List Nat)) (w : List (Nat × Bool)) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun l _ ih y => letterV G I l (ih y)) w x

@[expose] noncomputable def modelK (n k : Nat) (G I : List (List Nat)) (R : List (List (Nat × Bool))) :
    Bool :=
  andB
    (allN k fun g => allN n fun i =>
      andB (Nat.blt (getL (getLL G g) i) n) (Nat.beq (getL (getLL I g) (getL (getLL G g) i)) i))
    (List.rec (motive := fun _ => Bool) true
      (fun r _ ih => andB (allN n fun x => Nat.beq (walk G I r x) x) ih) R)

end CFSG.KC.CosetJ.Model

end
