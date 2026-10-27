module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

abbrev act33 (g : GL (Fin 3) (ZMod 3)) (u : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  Matrix.vecMul u (g : Matrix (Fin 3) (Fin 3) (ZMod 3))

@[expose] def FF79KGL33 : Prop :=
  ∀ (X : Subgroup (GL (Fin 3) (ZMod 3))) (v w₁ w₂ : Fin 3 → ZMod 3),
    LinearIndependent (ZMod 3) ![v, w₁, w₂] →
    (∃ τ ∈ X, act33 τ v = v ∧ act33 τ w₁ = -w₁ ∧ act33 τ w₂ = -w₂) →
    Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g v = v} = 8 →
    (∃ g ∈ X, ∃ h ∈ X, act33 g v = v ∧ act33 h v = v ∧ g * h ≠ h * g) →
    (∀ g ∈ X, (act33 g v = v ∨ act33 g v = -v) →
      (∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂}, act33 g w ∈ Submodule.span (ZMod 3) {w₁, w₂}) ∧
      ∃ d ∈ X, act33 d v = v ∧
        ((∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂}, act33 g w = act33 d w) ∨
          ∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂}, act33 g w = -act33 d w)) →
    (∃ g ∈ X, act33 g v ≠ v ∧ act33 g v ≠ -v) →
    ((∀ g ∈ X, ∀ w ∈ Submodule.span (ZMod 3) {w₁, w₂},
        act33 g w ∈ Submodule.span (ZMod 3) {w₁, w₂}) ∧
      ∀ u : Fin 3 → ZMod 3, u ∉ Submodule.span (ZMod 3) {w₁, w₂} →
        ∃ g ∈ X, act33 g v = u ∨ act33 g v = -u) ∨
    (∃ u₁ ∈ Submodule.span (ZMod 3) {w₁, w₂}, ∃ u₂ ∈ Submodule.span (ZMod 3) {w₁, w₂},
      LinearIndependent (ZMod 3) ![v, u₁, u₂] ∧
      (∀ g ∈ X, ∀ x ∈ ({v, -v, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3)),
        act33 g x ∈ ({v, -v, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3))) ∧
      (∃ g ∈ X, act33 g v = -v ∧ act33 g u₁ = u₁ ∧ act33 g u₂ = u₂) ∧
      (∃ g ∈ X, act33 g v = u₁ ∧ act33 g u₁ = v ∧ act33 g u₂ = u₂) ∧
      (∃ g ∈ X, act33 g v = u₁ ∧ act33 g u₁ = u₂ ∧ act33 g u₂ = v))

variable {G : Type} [Group G]

@[expose] def FF79KTypeLnNorm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (J P : Subgroup G), (n = 4 ∨ n = 5) →
    CFSG.IsQuasisimple ↥J → IsTypeLnq n 2 1 J → P ≤ J → IsSylowOf 3 P J →
    (∃ τ ∈ J, τ ∈ Nor P ∧ ∀ x ∈ P, τ * x * τ⁻¹ = x⁻¹) ∧
    {f : P → G | ∃ j ∈ J, j ∈ Nor P ∧ ∀ x : P, f x = j * x * j⁻¹}.ncard = 8 ∧
    (∃ j₁ ∈ J, ∃ j₂ ∈ J, j₁ ∈ Nor P ∧ j₂ ∈ Nor P ∧
      ∃ x ∈ P, j₁ * (j₂ * x * j₂⁻¹) * j₁⁻¹ ≠ j₂ * (j₁ * x * j₁⁻¹) * j₂⁻¹) ∧
    ∀ g ∈ Nor J, g ∈ Nor P → ∃ j ∈ J, j ∈ Nor P ∧ ∀ x ∈ P, g * x * g⁻¹ = j * x * j⁻¹

end CFSG.RankThree.PartTwo.Sec21.FF79
