module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped commutatorElement

@[expose] def g47Up (S : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  Matrix.fromBlocks 1 S 0 1

@[expose] def g47Lo (T : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  Matrix.fromBlocks 1 0 T 1

structure G47Coord {G : Type} [Group G] (K U B N : Subgroup G)
    (κ : G → (Fin 4 ⊕ Fin 4 → ZMod 2)) : Prop where
  add : ∀ k₁ ∈ K, ∀ k₂ ∈ K, κ (k₁ * k₂) = κ k₁ + κ k₂
  eq_zero_iff : ∀ k ∈ K, κ k = 0 ↔ k ∈ N
  left_surj : ∀ x : Fin 4 → ZMod 2, ∃ u ∈ U, κ u = Sum.elim x (0 : Fin 4 → ZMod 2)
  right_surj : ∀ y : Fin 4 → ZMod 2, ∃ b ∈ B, κ b = Sum.elim (0 : Fin 4 → ZMod 2) y
  right_of_U : ∀ u ∈ U, ∀ i : Fin 4, κ u (Sum.inr i) = 0
  left_of_B : ∀ b ∈ B, ∀ i : Fin 4, κ b (Sum.inl i) = 0
  sq_iff : ∀ k ∈ K, (k * k = 1 ↔
    dotProduct (fun i => κ k (Sum.inl i)) (fun i => κ k (Sum.inr i)) = 0)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
