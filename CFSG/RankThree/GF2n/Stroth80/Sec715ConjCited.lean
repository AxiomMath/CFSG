module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open
open scoped Matrix

@[expose] def Omega8LongRootRankStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (H : Type) [Group H] (φ : H →* GL (Fin 4 ⊕ Fin 4) K),
    φ.range = StatedOmega (StatedQuadPlus 4 K) →
  ∀ (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (ρ : H →* (X ≃ₗ[K] X)), (∀ h : H, φ h = 1 → ρ h = 1) →
    (∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρ h x ∈ S) → S = ⊥ ∨ S = ⊤) →
    (∃ h : H, ρ h ≠ 1) → Module.finrank K X ≤ 16 →
    Module.finrank K X = 8 ∧
    ∀ u w : Fin 4 ⊕ Fin 4 → K, LinearIndependent K ![u, w] →
      StatedQuadPlus 4 K u = 0 → StatedQuadPlus 4 K w = 0 → StatedQuadPlus 4 K (u + w) = 0 →
      ∀ h h' : H,
        (∀ v, ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ v - v ∈
          Submodule.span K {u, w}) →
        (∀ v, StatedQuadPlus 4 K (v + u) - StatedQuadPlus 4 K v - StatedQuadPlus 4 K u = 0 →
          StatedQuadPlus 4 K (v + w) - StatedQuadPlus 4 K v - StatedQuadPlus 4 K w = 0 →
          ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ v = v) →
        (∀ v, ((φ h' : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ v - v ∈
          Submodule.span K {u, w}) →
        (∀ v, StatedQuadPlus 4 K (v + u) - StatedQuadPlus 4 K v - StatedQuadPlus 4 K u = 0 →
          StatedQuadPlus 4 K (v + w) - StatedQuadPlus 4 K v - StatedQuadPlus 4 K w = 0 →
          ((φ h' : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ v = v) →
        φ h ≠ 1 →
        Module.finrank K (LinearMap.range ((ρ h : X →ₗ[K] X) - LinearMap.id)) = 2 ∧
        ∃ c : K, ∀ x : X, ρ h' x - x = c • (ρ h x - x)

end CFSG.RankThree.GF2n.Stroth80
