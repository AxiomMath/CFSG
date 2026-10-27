module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open scoped Matrix

@[expose] def IsValentiner (K : Type) [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) : Prop :=
  Nat.card K = 4 ∧
    (∀ g ∈ Γ, ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) ∧
    IsHat ↥Γ ↥(alternatingGroup (Fin 6)) ∧
    ∀ g ∈ Subgroup.center ↥Γ, ∃ c : K,
      (((g : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1

@[expose] def fixNat {K : Type} [Field K] (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K))
    (B : Subgroup ↥Γ) : Set (Fin 3 → K) :=
  {w | ∀ γ ∈ B,
    (((γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w}

@[expose] def OffNat {K : Type} [Field K] (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K))
    (F : Subgroup ↥Γ) : Prop :=
  F ≠ ⊥ ∧ (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧ (∀ a ∈ F, a ^ 2 = 1) ∧
    ∀ B : Subgroup ↥Γ, B ≤ F →
      Nat.card B * Nat.card ↥(fixNat Γ B) ≤ Nat.card F * Nat.card ↥(fixNat Γ F)

@[expose] def D35ValCore : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)),
    IsValentiner K Γ →
    ∀ (α : (↥Γ ⧸ Subgroup.center ↥Γ) ≃* (↥Γ ⧸ Subgroup.center ↥Γ)) (E F : Subgroup ↥Γ),
      OffNat Γ E → OffNat Γ F →
      (E.map (QuotientGroup.mk' (Subgroup.center ↥Γ))).map α.toMonoidHom =
        F.map (QuotientGroup.mk' (Subgroup.center ↥Γ)) →
      ∃ (β : ↥Γ ≃* ↥Γ) (Φ : (Fin 3 → K) ≃+ (Fin 3 → K)),
        (∀ γ : ↥Γ, QuotientGroup.mk' (Subgroup.center ↥Γ) (β γ) =
          α (QuotientGroup.mk' (Subgroup.center ↥Γ) γ)) ∧
        ∀ (γ : ↥Γ) (w : Fin 3 → K),
          Φ ((((γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
            ((((β γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ w)

end CFSG.Quasithin
