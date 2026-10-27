module

public import CFSG.Quasithin.Background.B4ModelsSporadic

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

@[expose] def MathieuSmallIrr24 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L : Subgroup (MulAut W), Nonempty (↥L ≃* NativeSporadic.Carrier .M24) →
      (∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
      Nat.card W ≤ 2 ^ 36 → MathieuCode24 L ⊤ ⊥ ∨ MathieuCocode24 L ⊤ ⊥

@[expose] def MathieuSmallIrr23 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L : Subgroup (MulAut W), Nonempty (↥L ≃* NativeSporadic.Carrier .M23) →
      (∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
      Nat.card W ≤ 2 ^ 24 → MathieuCode23 L ⊤ ⊥ ∨ MathieuCocode23 L ⊤ ⊥

@[expose] def MathieuSmallIrr22 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L : Subgroup (MulAut W), Nonempty (↥L ≃* NativeSporadic.Carrier .M22) →
      (∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
      Nat.card W ≤ 2 ^ 30 → MathieuCode22 L ⊤ ⊥ ∨ MathieuCocode22 L ⊤ ⊥

@[expose] def MathieuSmallIrr12 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L : Subgroup (MulAut W), Nonempty (↥L ≃* NativeSporadic.Carrier .M12) →
      (∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
      Nat.card W ≤ 2 ^ 24 → M12Ten L ⊤ ⊥

end CFSG.Quasithin
