module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup

@[expose] def Model3A (Y : Type*) [Group Y] (V : Subgroup Y) (q : ℕ) : Prop :=
  Nat.card ↥(center ↥V) = q ∧ ∀ z ∈ center ↥V, z * z = 1

@[expose] def Model3B (Y : Type*) [Group Y] (V : Subgroup Y) : Prop :=
  ∀ x : Y, x * x = 1 → ∃ y : Y, y⁻¹ * x * y ∈ (center ↥V).map V.subtype

@[expose] def Model3C (Y : Type*) [Group Y] (V : Subgroup Y) : Prop :=
  ∀ τ : Y, ¬ IsPGroup 2 ↥((center ↥V).map V.subtype ⊔
      ((center ↥V).map V.subtype).map (MulAut.conj τ⁻¹).toMonoidHom) →
    V ⊔ V.map (MulAut.conj τ⁻¹).toMonoidHom = ⊤

structure Model3Concl (Y : Type*) [Group Y] (V : Subgroup Y) (q : ℕ) : Prop where
  a : Model3A Y V q
  b : Model3B Y V
  c : Model3C Y V

@[expose] def Model3TildeA (X : Type*) [Group X] (q : ℕ) : Prop :=
  ∀ R : Sylow 2 X, Model3A X (R : Subgroup X) q

@[expose] def Model3TildeB (X : Type*) [Group X] : Prop :=
  ∀ R : Sylow 2 X, Model3B X (R : Subgroup X)

@[expose] def Model3TildeC (X : Type*) [Group X] : Prop :=
  ∀ R : Sylow 2 X, Model3C X (R : Subgroup X)

structure Model3Tilde (X : Type*) [Group X] (q : ℕ) : Prop where
  a : Model3TildeA X q
  b : Model3TildeB X
  c : Model3TildeC X

structure Model3Sub {G : Type*} [Group G] (Y V : Subgroup G) (q : ℕ) : Prop where
  le : V ≤ Y
  card_center : Nat.card ↥(V ⊓ centralizer (V : Set G)) = q
  sq_center : ∀ z ∈ V ⊓ centralizer (V : Set G), z * z = 1
  involution : ∀ x ∈ Y, x * x = 1 → ∃ y ∈ Y, y⁻¹ * x * y ∈ V ⊓ centralizer (V : Set G)
  generation : ∀ τ ∈ Y,
    ¬ IsPGroup 2 ↥((V ⊓ centralizer (V : Set G)) ⊔
      (V ⊓ centralizer (V : Set G)).map (MulAut.conj τ⁻¹).toMonoidHom) →
      V ⊔ V.map (MulAut.conj τ⁻¹).toMonoidHom = Y

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
