module

public import CFSG.LocalAnalysis.StandardType.GGHalfCoords

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

structure GGHalfTorusFrame {G : Type} [Group G] (Bs X : Subgroup G) {N : ℕ}
    (T : Subgroup (SpecialLinearGroup (Fin (N + 1)) F2))
    (ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G) : Prop where
  range : ψ.range = X
  inj : Function.Injective ψ
  torus_le : T.map ψ ≤ Bs
  act : ∀ b ∈ Bs, ∃ t ∈ T, ∀ l ∈ X, b * l * b⁻¹ = ψ t * l * (ψ t)⁻¹

structure GGHalfLeviData {G : Type} [Group G] (Bs L J K : Subgroup G) (x y : G) (m : ℕ)
    (ψ₁ ψ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : Prop where
  frameL : GGHalfTorusFrame Bs L (halfTorus (m + 1 + 1)) ψ₁
  frameK : GGHalfTorusFrame Bs K (halfTorusK (m + 1 + 1)) ψ₂
  levi₁ : (ψ₁.comp (slLower2Hom m)).range = J
  levi₂ : (ψ₂.comp (slUpper2Hom m)).range = J
  suppY : ∃ t ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩),
    ∀ l ∈ L, y * l * y⁻¹ = ψ₁ t * l * (ψ₁ t)⁻¹
  suppX : ∃ t ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, Nat.lt_succ_self _⟩),
    ∀ k ∈ K, x * k * x⁻¹ = ψ₂ t * k * (ψ₂ t)⁻¹

@[expose] def GGTypeAHalfLeviInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J →
    GGTypeAHalfNbr p B Bs x L D J (m + 1 + 1) y K → J ≤ K →
    ∃ ψ₁ ψ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G,
      GGHalfLeviData Bs L J K x y m ψ₁ ψ₂

end CFSG.StandardType

end
