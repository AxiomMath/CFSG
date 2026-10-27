module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open

@[expose] def HKSNormalStatement : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (Ω : Type) [Finite Ω] [MulAction H Ω] [FaithfulSMul H Ω]
    (m : ℕ), 2 ≤ m → Nat.card Ω = 2 ^ m + 1 → MulAction.IsMultiplyPretransitive H Ω 2 →
    ∀ (α : Ω) (R : Subgroup H), R ≤ MulAction.stabilizer H α →
      (R.subgroupOf (MulAction.stabilizer H α)).Normal → IsElemAbelian 2 R →
      (∀ β γ : Ω, β ≠ α → γ ≠ α → ∃! r : R, (r : H) • β = γ) →
      ∃ L : Subgroup H, L.Normal ∧ IsSimpleGroup L ∧
        Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) ∧
        MulAction.IsMultiplyPretransitive L Ω 2 ∧ R ≤ L

@[expose] def SL2FixedLineDimStatement : Prop :=
  ∀ (k e : ℕ), 2 ≤ k → 1 ≤ e → ∀ (V : Type) [AddCommGroup V] [Module (GaloisField 2 k) V]
    [Module.Finite (GaloisField 2 k) V]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (k * e)) →*
      (V ≃ₗ[GaloisField 2 k] V)),
    (∀ W : Submodule (GaloisField 2 k) V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∀ P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (k * e))),
      IsPGroup 2 P → Nat.card P = 2 ^ (k * e) →
      (∃ b : V, b ≠ 0 ∧ (∀ g ∈ P, ρ g b = b) ∧
        ∀ v : V, (∀ g ∈ P, ρ g v = v) → ∃ s : GaloisField 2 k, v = s • b) →
      ∃ x : ℕ, Module.finrank (GaloisField 2 k) V = 2 ^ (x * e)

@[expose] def Ovoid37Statement : Prop :=
  HKSNormalStatement → ∀ (k n : ℕ), 2 ≤ k → 2 < n →
    ∀ (E : Type) [AddCommGroup E] [Module (GaloisField 2 k) E] [Module.Finite (GaloisField 2 k) E],
    Module.finrank (GaloisField 2 k) E = 2 * n →
    ∀ (Bf : LinearMap.BilinForm (GaloisField 2 k) E) (Qf : E → GaloisField 2 k),
    (∀ (a : GaloisField 2 k) (e : E), Qf (a • e) = a ^ 2 * Qf e) →
    (∀ e f : E, Qf (e + f) = Qf e + Qf f + Bf e f) →
    ∀ (H : Subgroup (E ≃ₗ[GaloisField 2 k] E)), (∀ h ∈ H, ∀ e : E, Qf (h e) = Qf e) →
    ∀ (b : E), Qf b = 0 →
    ∀ (U : Submodule (GaloisField 2 k) E), (∀ u ∈ U, Qf u = 0) →
      Module.finrank (GaloisField 2 k) U = n → b ∈ U →
    ∀ (Λ : Subgroup (E ≃ₗ[GaloisField 2 k] E)), Λ ≤ H →
      Nat.card Λ = Nat.card (GaloisField 2 k) ^ (n - 1) →
      (∀ t ∈ Λ, ∀ t' ∈ Λ, t * t' = t' * t) → (∀ t ∈ Λ, t * t = 1) → (∀ t ∈ Λ, t b = b) →
    ∀ (P : Set E), b ∈ P → (∀ p ∈ P, p ≠ 0 ∧ Qf p = 0) →
      (∀ p ∈ P, ∀ c : GaloisField 2 k, c ≠ 0 → c • p ∈ P) →
      (∀ h ∈ H, ∀ p ∈ P, h p ∈ P) →
      (∀ p ∈ P, ∀ p' ∈ P, (∀ c : GaloisField 2 k, p' ≠ c • p) → Bf p p' ≠ 0) →
      Submodule.span (GaloisField 2 k) P = ⊤ →
      (∀ t ∈ Λ, t ≠ 1 → ∀ p ∈ P, (∀ c : GaloisField 2 k, p ≠ c • b) →
        t p ∈ Submodule.span (GaloisField 2 k) {p} → False) →
      (∀ h ∈ H, Submodule.map (h : E →ₗ[GaloisField 2 k] E)
          (Submodule.span (GaloisField 2 k) {b}) = Submodule.span (GaloisField 2 k) {b} →
        ∀ t ∈ Λ, h * t * h⁻¹ ∈ Λ) →
      (∃ h ∈ H, Submodule.map (h : E →ₗ[GaloisField 2 k] E)
          (Submodule.span (GaloisField 2 k) {b}) ≠ Submodule.span (GaloisField 2 k) {b}) →
      ∃ L : Subgroup (E ≃ₗ[GaloisField 2 k] E), L ≤ H ∧ (L.subgroupOf H).Normal ∧
        IsSimpleGroup L ∧
        Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (k * (n - 1)))) ∧
        Λ ≤ L ∧
        Submodule.span (GaloisField 2 k)
          (Set.range fun ℓ : L => ((ℓ : E ≃ₗ[GaloisField 2 k] E)) b) = ⊤ ∧
        (∀ p ∈ P, ∃ h ∈ H, Submodule.map (h : E →ₗ[GaloisField 2 k] E)
          (Submodule.span (GaloisField 2 k) {b}) = Submodule.span (GaloisField 2 k) {p})

@[expose] def Module37Statement : Prop :=
  SL2FixedLineDimStatement → ∀ (k n : ℕ), 2 ≤ k → 2 < n →
    ∀ (E : Type) [AddCommGroup E] [Module (GaloisField 2 k) E] [Module.Finite (GaloisField 2 k) E],
    Module.finrank (GaloisField 2 k) E = 2 * n →
    ∀ (L : Subgroup (E ≃ₗ[GaloisField 2 k] E)),
    Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (k * (n - 1)))) →
    ∀ (b : E), b ≠ 0 →
    Submodule.span (GaloisField 2 k)
      (Set.range fun ℓ : L => ((ℓ : E ≃ₗ[GaloisField 2 k] E)) b) = ⊤ →
    ∀ (Λ : Subgroup (E ≃ₗ[GaloisField 2 k] E)), Λ ≤ L →
      Nat.card Λ = 2 ^ (k * (n - 1)) → (∀ t ∈ Λ, t b = b) →
      (∀ v : E, (∀ t ∈ Λ, t v = v) → ∃ s : GaloisField 2 k, v = s • b) → n = 4

end CFSG.RankThree.GF2n.Stroth80
