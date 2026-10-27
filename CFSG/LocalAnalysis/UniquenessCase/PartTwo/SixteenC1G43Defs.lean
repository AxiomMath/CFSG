module

public import CFSG.LocalAnalysis.WeakClosure81.SixFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G]

structure E16Lift (V B : Subgroup G) (z : G) (P : Subgroup G) : Prop where
  mem_z : z ∈ V
  ne_one : z ≠ 1
  le : P ≤ V
  relIndex_eq : P.relIndex V = 2
  fixed_iff : ∀ v ∈ V, (∀ b ∈ B, b * v * b⁻¹ = v) ↔ (v = 1 ∨ v = z)
  act_of_mem : ∀ b ∈ B, ∀ v ∈ P, b * v * b⁻¹ = v ∨ b * v * b⁻¹ = v * z
  mem_of_act : ∀ b ∈ B, b ∉ centralizer (V : Set G) → ∀ v ∈ V,
    (b * v * b⁻¹ = v ∨ b * v * b⁻¹ = v * z) → v ∈ P
  le_closure : P ≤ Subgroup.closure
    {v : G | v ∈ V ∧ ∃ b ∈ B, b ∉ centralizer (V : Set G) ∧ b * v * b⁻¹ = v}
  exists_move : ∃ b ∈ B, ∃ v ∈ P, b * v * b⁻¹ ≠ v

@[expose] def PrimHalf (M V : Subgroup G) (g : G) : Prop :=
  V ⊓ centralizer ((BOf M V g : Subgroup G) : Set G) ≤ conjSubgroup V g ∧
    ∀ b ∈ BOf M V g, b ∉ V → ∀ v ∈ V, ⁅v, b⁆ ∈ V ⊓ conjSubgroup V g → v ∈ conjSubgroup M g

structure PrimGeom (M V : Subgroup G) (g : G) : Prop where
  half : PrimHalf M V g
  relIndex_U : (UOf M V g).relIndex V = 2
  card_U : Nat.card ↥(UOf M V g) = 32
  card_B : Nat.card ↥(BOf M V g) = 32
  card_N : Nat.card ↥(NOf M V g) = 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
