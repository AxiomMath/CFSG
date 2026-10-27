module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section Vocabulary

variable {W : Type*} [CommGroup W]

@[expose] def SecIsoOn (X : Subgroup (MulAut W)) (A A₀ B B₀ : Subgroup W) : Prop :=
  A₀ ≤ A ∧ B₀ ≤ B ∧ StableUnder X A ∧ StableUnder X A₀ ∧ StableUnder X B ∧ StableUnder X B₀ ∧
    ∃ β : ↥A →* W, (∀ a : ↥A, β a ∈ B) ∧ (∀ a : ↥A, β a ∈ B₀ ↔ (a : W) ∈ A₀) ∧
      (∀ b ∈ B, ∃ a : ↥A, β a * b⁻¹ ∈ B₀) ∧
      ∀ x ∈ X, ∀ a a' : ↥A, (a' : W) = x a → β a' * (x (β a))⁻¹ ∈ B₀

@[expose] def IsIndivisible (Y : Subgroup (MulAut W)) : Prop :=
  ∀ U₁ U₂ : Subgroup W, StableUnder Y U₁ → StableUnder Y U₂ → U₁ ⊔ U₂ = ⊤ → U₁ = ⊤ ∨ U₂ = ⊤

@[expose] def IsBasicModule (Y : Subgroup (MulAut W)) : Prop :=
  IsIndivisible Y ∧
    ∀ U : Subgroup W, StableUnder Y U → (∀ y ∈ Y, (∀ u ∈ U, y u = u) → y = 1) → U = ⊤

@[expose] def IrrSpanTrans (Y H : Subgroup (MulAut W)) : Prop :=
  (⨆ I ∈ irrSet H, I) = ⊤ ∧
    ∀ I ∈ irrSet H, ∀ J ∈ irrSet H, ∃ g ∈ Y,
      SecIsoOn H (I.map (g : MulAut W).toMonoidHom ⊔ fixV H) (fixV H) (J ⊔ fixV H) (fixV H)

end Vocabulary

@[expose] def W4Lem12_5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y : Subgroup (MulAut W),
      (∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥) →
      IsBasicModule Y →
      ∀ H : Subgroup (MulAut W), H ≠ ⊥ → H ≤ Y → (H.subgroupOf Y).Normal →
        (Odd (Nat.card H) → IrrSpanTrans Y H) ∧
        ∀ L : Subgroup (MulAut W), IsComponentOf L Y →
          H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom →
            IrrSpanTrans Y H ∧ (⨆ I ∈ irrSet L, I) ⊔ fixV L = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
