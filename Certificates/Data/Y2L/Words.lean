module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Algebra.Group.Commutator

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open scoped commutatorElement

@[expose] def y2l_rels26List (n : ℕ) (e : Bool) : List (FreeGroup (Fin 5)) :=
  let u : FreeGroup (Fin 5) := FreeGroup.of 0
  let v : FreeGroup (Fin 5) := FreeGroup.of 1
  let w : FreeGroup (Fin 5) := FreeGroup.of 2
  let r : FreeGroup (Fin 5) := FreeGroup.of 3
  let s : FreeGroup (Fin 5) := FreeGroup.of 4
  [⁅u, v⁆, ⁅u, w⁆, ⁅v, w⁆, u ^ 2 ^ n, v ^ 2 ^ n, w ^ 2 ^ n, r ^ 2,
    r⁻¹ * s * r * s, r⁻¹ * u * r * w, r⁻¹ * v * r * v, r⁻¹ * w * r * u,
    s⁻¹ * u * s * v⁻¹, s⁻¹ * v * s * w⁻¹, s⁻¹ * w * s * (u * v⁻¹ * w)⁻¹,
    s ^ 4 * (if e then (u * w)⁻¹ else 1)]

@[expose] def y2l_ws26 (n : ℕ) (e : Bool) : List (List (Fin 5 × Bool)) :=
  (y2l_rels26List n e).map FreeGroup.toWord

@[expose] def y2l_ws7 (k : ℕ) : List (List (Fin 5 × Bool)) :=
  ([(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)] :
      List (ℕ × ℕ × ℕ)).map fun t =>
    List.replicate (k * t.1) (0, true) ++ List.replicate (k * t.2.1) (1, true) ++
      List.replicate (k * t.2.2) (2, true)

@[expose] def y2l_invW (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def y2l_subst (W : List (List (ℕ × Bool))) (r : List (Fin 5 × Bool)) :
    List (ℕ × Bool) :=
  r.flatMap fun l => if l.2 then W.getD l.1 [] else y2l_invW (W.getD l.1 [])

end CFSG.OddStandard.HigherRank.G2Three.Sec2
