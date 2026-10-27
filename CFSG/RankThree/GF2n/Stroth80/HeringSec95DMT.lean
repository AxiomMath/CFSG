module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1A

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Matrix MatrixGroups

@[expose] def Step95ModuleStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (bw : W →ₗ[K] W →ₗ[K] K) (qw : W → K),
    (∀ w, bw w w = 0) → (∀ w, (∀ w', bw w w' = 0) → w = 0) →
    (∀ γ w w', bw (Act γ w) (Act γ w') = bw w w') →
    (∀ (c : K) w, qw (c • w) = c ^ 2 * qw w) →
    (∀ w w', qw (w + w') = qw w + qw w' + bw w w') → (∀ γ w, qw (Act γ w) = qw w) →
    ∀ X : Submodule K W,
      (∀ a a' : K, ∀ w, Act (HS9.M1.uSL a, HS9.M1.uSL a') w - w ∈ X) →
      (∀ a a' : K, ∀ x ∈ X, Act (HS9.M1.uSL a, HS9.M1.uSL a') x = x) →
      (∀ w, (∀ a a' : K, Act (HS9.M1.uSL a, HS9.M1.uSL a') w = w) → w ∈ X) →
      (∃ g h : SL(2, K), (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∧
        (h : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∧
        IsCompl X (X.map ((Act (g, h) : W ≃ₗ[K] W) : W →ₗ[K] W))) →
      (∀ w, (∀ γ, Act γ w = w) → w = 0) →
      (∃ Θ : AddSubgroup (W →ₗ[K] Matrix (Fin 2) (Fin 2) K),
        (∀ θ ∈ Θ, ∀ (a a' : K) w,
          θ (Act (HS9.M1.uSL a, HS9.M1.uSL a') w) = HS9.M1.uMat a * θ w * (HS9.M1.uMat a')ᵀ) ∧
        ∀ x ∈ X, (∀ θ ∈ Θ, θ x = 0) → x = 0) →
      ∃ (Y₁ Y₂ : Type) (_ : AddCommGroup Y₁) (_ : Module K Y₁) (_ : AddCommGroup Y₂)
        (_ : Module K Y₂) (β₁ : Y₁ →ₗ[K] Y₁ →ₗ[K] K) (β₂ : Y₂ →ₗ[K] Y₂ →ₗ[K] K)
        (c : W ≃ₗ[K] (Fin 2 → Y₁) × (Fin 2 → Y₂)),
        (∀ y, β₁ y y = 0) ∧ (∀ y, (∀ y', β₁ y y' = 0) → y = 0) ∧
        (∀ y, β₂ y y = 0) ∧ (∀ y, (∀ y', β₂ y y' = 0) → y = 0) ∧
        (∀ γ w, c (Act γ w) = HS9.M1.actW (γ.1 : Matrix (Fin 2) (Fin 2) K)
          (γ.2 : Matrix (Fin 2) (Fin 2) K) (c w)) ∧
        ∀ w w', bw w w' = HS9.M1.formW β₁ β₂ (c w) (c w')

end CFSG.RankThree.GF2n.Stroth80
