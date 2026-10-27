module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.RankThree.PartTwo.KFacts

open scoped Matrix

@[expose] def LineBadOne (δ v : Fin 3 → ZMod 3) : Prop :=
  ∃ l m : ZMod 3, m ≠ 0 ∧ v = l • Pi.single 0 1 + m • δ

@[expose] def LineBadTwo (v : Fin 3 → ZMod 3) : Prop := v 0 = 0 ∧ v 2 ≠ 0

instance (δ v : Fin 3 → ZMod 3) : Decidable (LineBadOne δ v) := by
  unfold LineBadOne
  infer_instance

instance (v : Fin 3 → ZMod 3) : Decidable (LineBadTwo v) := by
  unfold LineBadTwo
  infer_instance

@[expose] def lineMatX (r q : ZMod 3) (δ : Fin 3 → ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![1, r * δ 0, q * δ 0; 0, 1 + r * δ 1, q * δ 1; 0, r * δ 2, 1 + q * δ 2]

@[expose] def lineMatY (t : ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![1, 0, 0; 0, 1, 0; t, 0, 1]

theorem lines_cases : ∀ (t r q : ZMod 3) (δ : Fin 3 → ZMod 3), t ≠ 0 → (r ≠ 0 ∨ q ≠ 0) →
    (δ 1 ≠ 0 ∨ δ 2 ≠ 0) → (δ 2 ≠ 0 ∨ δ 1 = 0) → lineMatX r q δ *ᵥ δ = δ →
    LineBadTwo (lineMatX r q δ *ᵥ Pi.single 1 1) ∨
    LineBadOne δ (lineMatY t *ᵥ Pi.single 0 1) ∨
    LineBadTwo ((lineMatX r q δ * lineMatY t) *ᵥ Pi.single 0 1) ∨
    LineBadTwo ((lineMatX r q δ * (lineMatY t * lineMatY t)) *ᵥ Pi.single 0 1) ∨
    LineBadTwo ((lineMatX r q δ * lineMatX r q δ * lineMatY t) *ᵥ Pi.single 0 1) ∨
    LineBadTwo ((lineMatX r q δ * lineMatX r q δ * (lineMatY t * lineMatY t)) *ᵥ
      Pi.single 0 1) := by
  decide +kernel

end CFSG.RankThree.PartTwo.KFacts
