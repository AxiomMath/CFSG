module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.KG

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def cntN (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f k))) N

@[expose] noncomputable def isOne (n c : Nat) : Bool := Nat.beq c (one n)

@[expose] noncomputable def ordGo (n c : Nat) (k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun acc => isOne n acc)
    (fun _ ih acc => letB acc fun a => andB (notB (isOne n a)) (ih (mul n a c))) k

@[expose] noncomputable def ordK (n c m : Nat) : Bool := ordGo n c (Nat.sub m 1) c

@[expose] noncomputable def evalWK (n a b : Nat) (w : List Bool) : Nat :=
  List.rec (motive := fun _ => Nat) (one n)
    (fun x _ ih => mul n (Bool.rec (motive := fun _ => Nat) a b x) ih) w

@[expose] noncomputable def pairK (n a b : Nat) (ws : List (List Bool × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun w m => ordK n (evalWK n a b w) m) p)
      ih) ws

@[expose] noncomputable def memL (c : Nat) (L : List Nat) : Bool := anyL L fun x => Nat.beq x c

@[expose] noncomputable def cubeOne (n c : Nat) : Bool := isOne n (pow n c 3)

@[expose] noncomputable def pow2K (n x : Nat) : List Nat := [one n, x, pow n x 2]

@[expose] noncomputable def pow3K (n x y : Nat) : List Nat :=
  [one n, x, pow n x 2, y, mul n x y, mul n (pow n x 2) y, pow n y 2, mul n x (pow n y 2),
    mul n (pow n x 2) (pow n y 2)]

@[expose] noncomputable def fibAt (n : Nat) (E : Nat → Nat) (a ob : Nat)
    (ws : List (List Bool × Nat)) (k : Nat) : Bool :=
  letB (E k) fun y => andB (ordK n y ob) (pairK n a y ws)

@[expose] noncomputable def centAt (n : Nat) (E : Nat → Nat) (a b k : Nat) : Bool :=
  letB (E k) fun s => impB (andB (comm n s a) (comm n s b)) (isOne n s)

@[expose] noncomputable def inCAt (n : Nat) (E : Nat → Nat) (r : Nat) (CL : List Nat) (k : Nat) :
    Bool :=
  letB (E k) fun g => impB (comm n g r) (memL g CL)

@[expose] noncomputable def inC3At (n : Nat) (E : Nat → Nat) (r : Nat) (CL : List Nat) (k : Nat) :
    Bool :=
  letB (E k) fun g => impB (andB (comm n g r) (cubeOne n g)) (memL g CL)

@[expose] noncomputable def e9K (n : Nat) (CL : List Nat) : Bool :=
  allL CL fun X => allL CL fun Y =>
    impB (andB (notB (isOne n X)) (andB (cubeOne n X) (andB (cubeOne n Y) (comm n X Y))))
      (orB (isOne n Y) (orB (Nat.beq Y X) (Nat.beq Y (pow n X 2))))

@[expose] noncomputable def e27K (n X : Nat) (CL : List Nat) : Bool :=
  allL CL fun Y => allL CL fun Z =>
    impB (comm n Y Z) (orB (memL Y (pow2K n X)) (memL Z (pow3K n X Y)))

@[expose] noncomputable def cent3K (n x : Nat) (CL : List Nat) : Bool :=
  allL CL fun y => impB (andB (cubeOne n y) (notB (memL y (pow2K n x))))
    (allL CL fun k => impB (comm n k y) (memL k (pow3K n x y)))

end CFSG.KC.Misc.KG

end
