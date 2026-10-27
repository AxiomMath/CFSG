module

public import CFSG.Permutation.FiveTransitive.EquivariantFiberOrbits
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.TupleFiberOrbits

open MulAction

@[expose] def projection
    {G X : Type*} [Group G] [MulAction G X] {k m : ℕ}
    (E : SubMulAction G (Fin m ↪ X)) (j : Fin k ↪ Fin m) :
    E → (Fin k ↪ X) := fun e => j.trans e.val

theorem projection_smul
    {G X : Type*} [Group G] [MulAction G X] {k m : ℕ}
    (E : SubMulAction G (Fin m ↪ X)) (j : Fin k ↪ Fin m)
    (g : G) (e : E) : projection E j (g • e) = g • projection E j e := rfl

@[expose] def fiber
    {G X : Type*} [Group G] [MulAction G X] {k m : ℕ}
    (E : SubMulAction G (Fin m ↪ X)) (j : Fin k ↪ Fin m) (b : Fin k ↪ X) :=
    EquivariantFiberOrbits.fiber (projection E j) (projection_smul E j) b

theorem card_orbits_eq
    {G X : Type*} [Group G] [MulAction G X] {k m : ℕ}
    (hk : IsMultiplyPretransitive G X k)
    (E : SubMulAction G (Fin m ↪ X)) (j : Fin k ↪ Fin m) (b : Fin k ↪ X) :
    Nat.card (orbitRel.Quotient G E) =
      Nat.card (orbitRel.Quotient (stabilizer G b) (fiber E j b)) := by
  let _ : IsPretransitive G (Fin k ↪ X) := hk
  exact EquivariantFiberOrbits.card_orbits_eq (projection E j) (projection_smul E j) b

end FiveTransitive.TupleFiberOrbits

end CFSG
