module

public import CFSG.Sporadic.Schreier.Enumeration
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4C

open CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] def q8Elems (r i j : Equiv.Perm (Fin n)) : List (Equiv.Perm (Fin n)) :=
  [1, r, i, i * r, j, j * r, i * j, i * j * r]

@[expose] def norms (L : List (Equiv.Perm (Fin n))) (i j h : Equiv.Perm (Fin n)) : Bool :=
  decide (h * i * h⁻¹ ∈ L) && decide (h * j * h⁻¹ ∈ L)

@[expose] def closedL (L : List (Equiv.Perm (Fin n))) (i j : Equiv.Perm (Fin n)) : Bool :=
  decide ((1 : Equiv.Perm (Fin n)) ∈ L) && L.all fun x =>
    decide (i * x ∈ L) && decide (j * x ∈ L) && decide (i⁻¹ * x ∈ L) && decide (j⁻¹ * x ∈ L)

@[expose] def letters (gens : List (Equiv.Perm (Fin n))) : List (Equiv.Perm (Fin n)) :=
  gens ++ gens.map (·⁻¹)

@[expose] def memberCheck (gens L : List (Equiv.Perm (Fin n))) (i j : Equiv.Perm (Fin n))
    (ws : List (Equiv.Perm (Fin n))) (σ : List (List ℕ)) : Bool :=
  decide (0 < ws.length) && decide (ws.getD 0 1 = 1) && (List.range ws.length).all fun k =>
    (List.range (letters gens).length).all fun l =>
      decide ((σ.getD k []).getD l 0 < ws.length) &&
        norms L i j ((ws.getD ((σ.getD k []).getD l 0) 1)⁻¹ * (letters gens).getD l 1 *
          ws.getD k 1)

@[expose] def treeStep (L : List (Equiv.Perm (Fin n))) (i j u gp gk : Equiv.Perm (Fin n))
    (d : Bool) : Bool :=
  !norms L i j (gp⁻¹ * gk) &&
    (if d then norms L i j (gk⁻¹ * (gp * u * gp⁻¹) * gk)
      else norms L i j (gp⁻¹ * (gk * u * gk⁻¹) * gp))

@[expose] def treeCheck (L U : List (Equiv.Perm (Fin n))) (i j : Equiv.Perm (Fin n))
    (ws : List (Equiv.Perm (Fin n))) (tree : List (ℕ × Bool × ℕ)) : Bool :=
  U.all (fun u => decide (u ∈ L) && !decide (u ^ 2 = 1) && decide (u ^ 4 = 1)) &&
    (List.range ws.length).all fun k => k == 0 ||
      (decide ((tree.getD k (0, false, 0)).1 < k) &&
        decide ((tree.getD k (0, false, 0)).2.2 < U.length) &&
        treeStep L i j (U.getD (tree.getD k (0, false, 0)).2.2 1)
          (ws.getD (tree.getD k (0, false, 0)).1 1) (ws.getD k 1) (tree.getD k (0, false, 0)).2.1)

@[expose] def nbrCheck (L : List (Equiv.Perm (Fin n))) (i j : Equiv.Perm (Fin n))
    (ws : List (Equiv.Perm (Fin n))) (allowed : List ℕ) : Bool :=
  (List.range ws.length).all fun k => decide (k ∈ allowed) ||
    !(norms L i j (ws.getD k 1 * i * (ws.getD k 1)⁻¹) &&
      norms L i j (ws.getD k 1 * j * (ws.getD k 1)⁻¹))

@[expose] def edgeCheck (L : List (Equiv.Perm (Fin n))) (i j g : Equiv.Perm (Fin n)) : Bool :=
  !norms L i j g && norms L i j (g * i * g⁻¹) && norms L i j (g * j * g⁻¹)

@[expose] def violates (T : List (Equiv.Perm (Fin n))) (i j c : Equiv.Perm (Fin n)) : Bool :=
  T.any (fun x => !decide (c * x * c⁻¹ ∈ T)) &&
    [i, j].any fun x => [c * i * c⁻¹, c * j * c⁻¹].any fun y => !decide (x * y = y * x)

@[expose] def sameSet (A B : List (Equiv.Perm (Fin n))) : Bool :=
  A.all (fun x => decide (x ∈ B)) && B.all (fun x => decide (x ∈ A))

@[expose] def identStep (r ρ : Equiv.Perm (Fin n)) (W L0 L1 : List (Equiv.Perm (Fin n)))
    (j : Equiv.Perm (Fin n)) : Bool :=
  !(decide (j * j = r) && decide (j * ρ * j⁻¹ = ρ⁻¹)) ||
    (sameSet (q8Elems r ρ j) L0 || sameSet (q8Elems r ρ j) L1 ||
      W.any (violates (q8Elems r ρ j) ρ j))

@[expose] def identCheck (r : Equiv.Perm (Fin n)) (reps C W L0 L1 : List (Equiv.Perm (Fin n))) :
    Bool :=
  reps.all fun ρ => !decide (ρ * ρ = r) || C.all fun j => identStep r ρ W L0 L1 (tab j)

@[expose] def badWit (u w : Equiv.Perm (Fin n)) : Bool :=
  !decide (w * u * w⁻¹ * u = u * (w * u * w⁻¹)) &&
    !decide (w * u * w⁻¹ * u * (w * u * w⁻¹)⁻¹ = u⁻¹)

@[expose] def identSqCheck (r : Equiv.Perm (Fin n)) (S W : List (Equiv.Perm (Fin n)))
    (Ls : List (List (Equiv.Perm (Fin n)))) : Bool :=
  S.all fun u => W.any (badWit u) || S.all fun v => !decide (v * u * v⁻¹ = u⁻¹) ||
    (Ls.any (sameSet (q8Elems r u v)) || W.any (violates (q8Elems r u v) u v))

end CFSG.ClassicalInvolution.Q3.TL4.E4C
