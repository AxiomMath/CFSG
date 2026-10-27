module

public import Init

public section

namespace CFSG.KC.Mat3

@[expose] def one3 : List Nat := [1, 0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def ent (a : List Nat) (i j : Nat) : Nat := a.getD (3 * i + j) 0

@[expose] def mul (p : Nat) (a b : List Nat) : List Nat :=
  [0, 1, 2].flatMap fun i => [0, 1, 2].map fun j =>
    (ent a i 0 * ent b 0 j + ent a i 1 * ent b 1 j + ent a i 2 * ent b 2 j) % p

@[expose] def vec (p : Nat) (x M : List Nat) : List Nat :=
  [0, 1, 2].map fun j => (x.getD 0 0 * ent M 0 j + x.getD 1 0 * ent M 1 j + x.getD 2 0 * ent M 2 j) % p

@[expose] def letter {m : Nat} (G Gi : List (List Nat)) (l : Fin m × Bool) : List Nat :=
  if l.2 then G.getD l.1.val [] else Gi.getD l.1.val []

@[expose] def word {m : Nat} (p : Nat) (G Gi : List (List Nat)) (w : List (Fin m × Bool)) :
    List Nat :=
  w.foldl (fun M l => mul p M (letter G Gi l)) one3

@[expose] def iter (p : Nat) (M x : List Nat) : Nat → List Nat
  | 0 => x
  | n + 1 => vec p (iter p M x n) M

@[expose] def periodIs (p : Nat) (M x : List Nat) (ℓ : Nat) : Bool :=
  iter p M x ℓ == x && (List.range ℓ).all fun k => k == 0 || iter p M x k != x

@[expose] def canon (p n : Nat) (a : List Nat) : Bool := a.length == n && a.all (· < p)

@[expose] def check (p m : Nat) (G Gi : List (List Nat)) (b : List Nat)
    (rels : List (List (Fin m × Bool))) (walks : List (List (Fin m × Bool) × Nat)) : Bool :=
  G.length == m && Gi.length == m && G.all (canon p 9) && Gi.all (canon p 9) && canon p 3 b &&
    (List.range m).all (fun i => mul p (G.getD i []) (Gi.getD i []) == one3 &&
      mul p (Gi.getD i []) (G.getD i []) == one3) &&
    rels.all (fun r => word p G Gi r == one3) &&
    walks.all fun wl => wl.2 == 0 || periodIs p (word p G Gi wl.1) b wl.2

end CFSG.KC.Mat3

end
