module

public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.StandardType.ZS

variable (p : ℕ) [Fact p.Prime]

@[expose] def H3Data {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (A : Subgroup (W ≃ₗ[ZMod p] W)) : Prop :=
  (LinearEquiv.neg (ZMod p) : W ≃ₗ[ZMod p] W) ∈ A ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ w ∈ A, IsRefl p x → IsRefl p y → IsRefl p w → orderOf (x * y) = 5 →
      ∃ g ∈ A, orderOf (x * (g * w * g⁻¹)) = 2 ∧ orderOf (y * (g * w * g⁻¹)) = 3

@[expose] def TFNegOfPrimThree : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (X : Subgroup (W ≃ₗ[ZMod p] W)), p ≠ 2 → ReflGen p X → QTwoLin.TransvectionFree X →
    SplitSupport X 3 → ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) →
    ¬ IsOrthType p (movedGroup X) →
    (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    LinearEquiv.neg (ZMod p) ∈ movedGroup X

@[expose] def TFPrimCorank (l : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (X Y : Subgroup (W ≃ₗ[ZMod p] W)) (d : ℕ), p ≠ 2 → Module.finrank (ZMod p) W = l + 1 →
    ReflGen p X → QTwoLin.TransvectionFree X → SplitSupport X l →
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) → ¬ IsOrthType p (movedGroup X) →
    (∀ z ∈ X, (∀ x ∈ X, z * x = x * z) → orderOf z ≤ 3) → DMax p X d → 3 < d →
    Y ≤ X → ReflGen p Y → SplitSupport Y (l - 1) → DMax p Y d →
    ∀ (g : Module.Basis (Fin (l - 1)) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
      (j₀ j₁ : Fin (l - 1)) (ζ : (ZMod p)ˣ), j₀ ≠ j₁ →
      (movedGroup Y = gmmn p g j₀ j₁ ζ ∧ ¬ (l = 3 ∧ orderOf ζ = 4) ∨
        movedGroup Y = g2mmn p g j₀ j₁ ζ ∧ ¬ (l = 3 ∧ (orderOf ζ ∣ 2 ∨ orderOf ζ = 4))) →
      (l = 3 ∧ d = 5 ∧ H3Data p (movedGroup X)) ∨
        (l = 4 ∧ d = 4 ∧ Nat.card X = 1152 ∧ Nat.card Y = 48)

@[expose] def TFDegenerateExt (l : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (X : Subgroup (W ≃ₗ[ZMod p] W)), p = 3 → 4 ≤ l → ReflGen p X →
    QTwoLin.TransvectionFree X → SplitSupport X l →
    (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    ∀ T ≤ X, (∀ s ∈ T, s ^ p = 1) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
      p ^ (l - 2) ≤ Nat.card T →
      (∀ s ∈ T, s ≠ 1 → Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace s) = 2) →
      ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) ∧ IsOrthType p (movedGroup X)

@[expose] def TFSmallThree : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (X : Subgroup (W ≃ₗ[ZMod p] W)), p ≠ 2 → ReflGen p X → QTwoLin.TransvectionFree X →
    SplitSupport X 3 → (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    Nat.card X ≤ 48 →
    ∃ g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X),
      movedGroup X = g2mmn p g 0 1 1

section Degenerate

variable {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] def DegenerateInput (G : Subgroup (U ≃ₗ[ZMod p] U)) (l : ℕ) : Prop :=
  p ≠ 2 → ReflGen p G → QTwoLin.TransvectionFree G → AbsIrred p G →
    ¬ Quasithin.SimsG4.IsImprimitiveOnV G → l + 2 ≤ Module.finrank (ZMod p) U →
  ∀ K ≤ G, ReflGen p K → SplitSupport K l →
    (∀ K' ≤ G, K ≤ K' → ReflGen p K' → SplitSupport K' l → K' = K) →
    (∃ x ∈ K, ∃ y ∈ K, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    ∀ a ∈ G, IsRefl p a →
      (¬ ∃ h ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set (U ≃ₗ[ZMod p] U)), a = h * c) →
      SplitSupport (Subgroup.closure (insert a (K : Set (U ≃ₗ[ZMod p] U)))) (l + 1) ∨
      ((∃ x ∈ Subgroup.closure (insert a (K : Set (U ≃ₗ[ZMod p] U))),
          ∃ y ∈ Subgroup.closure (insert a (K : Set (U ≃ₗ[ZMod p] U))),
            IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p) ∧
        ∀ K₁ ≤ K, ReflGen p K₁ → ∀ α : ℕ, 1 ≤ α → SplitSupport K₁ α →
          (∃ x ∈ K₁, ∃ y ∈ K₁, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
          ∃ B ≤ G, ReflGen p B ∧ K₁ ≤ B ∧ SplitSupport B (α + 2) ∧
            ∃ T ≤ B, (∀ s ∈ T, s ^ p = 1) ∧ (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) ∧
              p ^ α ≤ Nat.card T ∧ ∀ s ∈ T, s ≠ 1 →
                Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace s) = 2)

end Degenerate

end CFSG.StandardType.ZS

end
