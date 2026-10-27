module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.A38c16

open scoped MatrixGroups Matrix BigOperators

abbrev M3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def twistMat (t : ZMod 2) (x : SL(3, ZMod 2)) : M3 :=
  if t = 0 then (x : M3) else ((x⁻¹ : SL(3, ZMod 2)) : M3)ᵀ

@[expose] def tensorActT (t : ZMod 2 × ZMod 2) (g : SL(3, ZMod 2) × SL(3, ZMod 2)) (X : M3) : M3 :=
  twistMat t.1 g.1 * X * (twistMat t.2 g.2)ᵀ

@[expose] def fixSetT (t : ZMod 2 × ZMod 2) (E : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2))) :
    Set M3 :=
  {X | ∀ g ∈ E, tensorActT t g X = X}

@[expose] def Case3Check : Prop :=
  ∀ (t : ZMod 2 × ZMod 2) (Pi Q : AddSubgroup (ZMod 2 × ZMod 2)) (R : Finset (ZMod 2 × ZMod 2)),
    Pi ≠ ⊥ → Q ≤ Pi → (∀ r ∈ R, r ∈ Pi) → (∀ p ∈ Pi, ∃! r, r ∈ R ∧ p - r ∈ Q) →
    ∀ E : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2)),
      (∀ g ∈ E, g * g = 1) → (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (E ≠ ⊥ ∨ Q ≠ ⊥) →
      (Nat.card E * Nat.card Q) ^ 2 * ∏ r ∈ R, Nat.card (fixSetT (t + r) E) < 512 ^ Nat.card Pi

end CFSG.Quasithin.A38c16
