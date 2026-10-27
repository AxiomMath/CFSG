module

public import CFSG.Open.FischerThreeTranspositionMilestoneDefs
public import CFSG.Open.Defs

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

@[expose] def fiveForm (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) : ZMod 5 :=
  ∑ i : Fin n, x i.castSucc * y i.castSucc -
    (if ε then 1 else 2) * (x (Fin.last n) * y (Fin.last n))

@[expose] def fiveReflections (n : ℕ) (ε π : Bool) : Set (GL (Fin (n + 1)) (ZMod 5)) :=
  {g | ∃ v, fiveForm n ε v v ≠ 0 ∧ (IsSquare (fiveForm n ε v v) ↔ π = true) ∧
    ∀ x, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x =
      x - (2 * fiveForm n ε x v * (fiveForm n ε v v)⁻¹) • v}

@[expose] def fiveReflectionGroup (n : ℕ) (ε π : Bool) : Subgroup (GL (Fin (n + 1)) (ZMod 5)) :=
  Subgroup.closure (fiveReflections n ε π)

@[expose] def IsFiveReflectionModel (n : ℕ) (ε π : Bool) {G : Type*} [Group G] (D : Set G) :
    Prop :=
  CFSG.Open.fischerCentralQuotientModel D (fiveReflectionGroup n ε π) (fiveReflections n ε π)

end CFSG.OddTranspositions.PartThree
