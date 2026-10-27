module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.G2U

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def fldN (x o m : Nat) : Nat :=
  Nat.land (Nat.shiftRight x o) (Nat.sub (Nat.shiftLeft (nat_lit 1) m) (nat_lit 1))

@[expose] noncomputable def row2 (x y i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.xor acc (fldN y (Nat.mul 14 k) 14))
      (Nat.blt (nat_lit 0) (Nat.land x (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul 14 i) k))))) 14

@[expose] noncomputable def m2 (x y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (row2 x y i) (Nat.mul 14 i))) 14

@[expose] noncomputable def add9K (x y : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.mod x 3) (Nat.mod y 3)) 3)
    (Nat.mul 3 (Nat.mod (Nat.add (Nat.div x 3) (Nat.div y 3)) 3))

@[expose] noncomputable def mul9K (x y : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.mul (Nat.mod x 3) (Nat.mod y 3))
      (Nat.mul 2 (Nat.mul (Nat.div x 3) (Nat.div y 3)))) 3)
    (Nat.mul 3 (Nat.mod (Nat.add (Nat.mul (Nat.mod x 3) (Nat.div y 3))
      (Nat.mul (Nat.div x 3) (Nat.mod y 3))) 3))

@[expose] noncomputable def e9 (x k : Nat) : Nat := fldN x (Nat.mul 4 k) 4

@[expose] noncomputable def ent9 (x y i j : Nat) : Nat :=
  add9K (add9K (mul9K (e9 x (Nat.mul 3 i)) (e9 y j))
    (mul9K (e9 x (Nat.add (Nat.mul 3 i) 1)) (e9 y (Nat.add 3 j))))
    (mul9K (e9 x (Nat.add (Nat.mul 3 i) 2)) (e9 y (Nat.add 6 j)))

@[expose] noncomputable def m9 (x y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (ent9 x y (Nat.div k 3) (Nat.mod k 3))
      (Nat.mul 4 k))) 9

@[expose] noncomputable def mP (x y : Nat) : Nat :=
  Nat.lor (m9 (fldN x 0 36) (fldN y 0 36))
    (Nat.shiftLeft (m2 (Nat.shiftRight x 36) (Nat.shiftRight y 36)) 36)

@[expose] noncomputable def rows2 (m : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r _ ih => Nat.lor r (Nat.shiftLeft ih 14)) m

@[expose] noncomputable def codes9 (m : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r _ ih => Nat.lor r (Nat.shiftLeft ih 4)) m

@[expose] noncomputable def pairAt (I2 I9 : Nat) (E : Nat → Nat) (k : Nat) : Bool :=
  letB (E k) fun c => Bool.rec (motive := fun _ => Bool)
    (notB (Nat.beq (fldN c 0 36) I9)) (Nat.beq (fldN c 0 36) I9)
    (Nat.beq (Nat.shiftRight c 36) I2)

end CFSG.KC.Misc.G2U

end
