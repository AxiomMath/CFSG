module

public import Certificates.Data.Kernel.Spor.Fi24Kit

public section

namespace CFSG.KC.Fi24ThreeAK

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Kit

@[expose] noncomputable def sK (OL : Nat → Nat) (NT : Nat → Nat) (x : Nat) : Nat :=
  strictN (clsK OL NT (nat_lit 305530) x) (clsK OL NT (nat_lit 0))

@[expose] noncomputable def sKi (OL : Nat → Nat) (NT : Nat → Nat) (x : Nat) : Nat :=
  strictN (clsK OL NT (nat_lit 0) x) (clsK OL NT (nat_lit 305530))

@[expose] noncomputable def failOK (OL : Nat → Nat) (NT : Nat → Nat) (r q : Nat) : Bool :=
  notB (Nat.beq (strictN (clsK OL NT r q) (fun y => strictN (sK OL NT y) (clsK OL NT r)))
    (sKi OL NT q))

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) l

@[expose] noncomputable def nthL (l : List (List Nat)) (j : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun a _ ih j => Nat.rec (motive := fun _ => List Nat) a (fun k _ => ih k) j) l j

@[expose] noncomputable def cube (w : List Nat) : List Nat := w ++ (w ++ w)

@[expose] noncomputable def sixW (W : Nat → List Nat) (i j : Nat) : List (List Nat) :=
  [W (2 * i), W (2 * i + 1),
    W (2 * i) ++ (W (2 * i) ++ (W (2 * j) ++ (W (2 * j) ++ (W (2 * i) ++ W (2 * j))))),
    W (2 * j + 1) ++ (W (2 * j + 1) ++ (W (2 * i + 1) ++ (W (2 * i + 1) ++
      (W (2 * j + 1) ++ W (2 * i + 1))))),
    W (2 * j), W (2 * j + 1)]

@[expose] noncomputable def relW (S : List (List Nat)) (r : List (Nat × Bool)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun p _ ih => (fun g => Bool.rec (motive := fun _ => List Nat) (g ++ g) g p.2 ++ ih)
      (nthL S p.1)) r

@[expose] noncomputable def edgeAt (NW : Nat → Nat → Nat) (W : Nat → List Nat)
    (R : List (List (Nat × Bool))) (i j x : Nat) : Bool :=
  andB (allL (fun w => Nat.beq (wP NW (cube w) x) x) (sixW W i j))
    (allL (fun r => Nat.beq (wP NW (relW (sixW W i j) r) x) x) R)

@[expose] noncomputable def commAt (NW : Nat → Nat → Nat) (W : Nat → List Nat) (a b x : Nat) : Bool :=
  allL (fun u => allL (fun v => Nat.beq (wP NW (W (2 * a + u) ++ W (2 * b + v)) x)
    (wP NW (W (2 * b + v) ++ W (2 * a + u)) x)) [0, 1]) [0, 1]

@[expose] noncomputable def d4At (NW : Nat → Nat → Nat) (W : Nat → List Nat)
    (R : List (List (Nat × Bool))) (x : Nat) : Bool :=
  andB (allL (fun i => Nat.beq (wP NW (cube (W i)) x) x) [0, 1, 2, 3, 4, 5, 6, 7])
    (andB (edgeAt NW W R 0 1 x) (andB (edgeAt NW W R 1 2 x) (andB (edgeAt NW W R 1 3 x)
      (andB (commAt NW W 0 2 x) (andB (commAt NW W 0 3 x) (commAt NW W 2 3 x))))))

@[expose] noncomputable def conjOK (NW : Nat → Nat → Nat) (OL : Nat → Nat) (NT : Nat → Nat)
    (c : List Nat) (x : Nat) : Bool :=
  Nat.beq (wP NW (c ++ [18]) x) (strictN (wP NW c x) (sK OL NT))

end CFSG.KC.Fi24ThreeAK

end
