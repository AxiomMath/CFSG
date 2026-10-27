module

public import Certificates.Data.Kernel.Spor.Fi24Orb

public section

namespace CFSG.KC.Fi24Kn

open CFSG.KC.Loop CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun k _ => ih k) j) l i

@[expose] noncomputable def nthW (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih j => Nat.rec (motive := fun _ => List Nat) a (fun k _ => ih k) j) l i

@[expose] noncomputable def negB (b : Bool) : Bool := bIf(b, false, true)

@[expose] noncomputable def eqB (x y : Bool) : Bool := bIf(x, y, negB y)

@[expose] noncomputable def disjB (a b c d : Nat) : Bool :=
  negB (orB (Nat.beq a c) (orB (Nat.beq a d) (orB (Nat.beq b c) (Nat.beq b d))))

@[expose] noncomputable def knStep (TG : Nat → Nat → Nat) (FD : Nat → Nat) (L A B : Nat → Nat)
    (C : Nat → List Nat) (n i j : Nat) : Bool :=
  bIf(Nat.beq i j,
    andB (Nat.beq (walk TG (C i) (L i)) (nat_lit 0)) (andB (Nat.blt (A i) (B i)) (Nat.blt (B i) n)),
    andB (negB (andB (Nat.beq (A i) (A j)) (Nat.beq (B i) (B j))))
      (eqB (Nat.beq (fComp (FD (walk TG (C i) (L j)))) (nat_lit 2))
        (disjB (A i) (B i) (A j) (B j))))

@[expose] noncomputable def knOK (TG : Nat → Nat → Nat) (FD : Nat → Nat) (L A B : Nat → Nat)
    (C : Nat → List Nat) (n m : Nat) : Bool :=
  allBelow m (nat_lit 16) (fun i => allBelow m (nat_lit 16) (fun j => knStep TG FD L A B C n i j))

end CFSG.KC.Fi24Kn

end
