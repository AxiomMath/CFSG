module

public import CFSG.Quasithin.Background.SimsG4Defs
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def TFOrthOvergroup (p : ℕ) [Fact p.Prime] (m : ℕ) : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (X Y : Subgroup (U ≃ₗ[ZMod p] U)), Y ≤ X → ReflGen p X → QTwoLin.TransvectionFree X →
    SplitSupport X m → ReflGen p Y → SplitSupport Y m → IsOrthType p (movedGroup Y) →
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup Y) →
    (∃ x ∈ Y, ∃ y ∈ Y, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    IsOrthType p (movedGroup X)

@[expose] def TFOrthCorankOne (p : ℕ) [Fact p.Prime] (m : ℕ) : Prop :=
  4 ≤ m → ∀ (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (X Y : Subgroup (U ≃ₗ[ZMod p] U)), Y ≤ X → ReflGen p X → QTwoLin.TransvectionFree X →
    SplitSupport X m → ReflGen p Y → SplitSupport Y (m - 1) → IsOrthType p (movedGroup Y) →
    (p = 3 → ∃ x ∈ Y, ∃ y ∈ Y, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    (IsOrthType p (movedGroup X) ∧ ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X)) ∨
      (m = 4 ∧ p = 3 ∧ (∃ Q : QuadraticForm (ZMod p) U,
          (QuadraticMap.polarBilin Q).Nondegenerate ∧ ∀ g ∈ X, IsIsom p Q g) ∧
        ∃ x ∈ X, centralizerSpace Y ⊓ HardMathSupport.Kantor79.commutatorSpace X ≤
          (HardMathSupport.Kantor79.commutatorSpace Y).map (x : U →ₗ[ZMod p] U))

@[expose] def TFDegThree (p : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → ∀ (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U],
    Module.finrank (ZMod p) U = 4 → ∀ X : Subgroup (U ≃ₗ[ZMod p] U), ReflGen p X →
    QTwoLin.TransvectionFree X → SplitSupport X 3 →
    (IsOrthType p (movedGroup X) ∧ ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X)) ∨
      (∃ g ∈ X, ∃ ζ : ZMod p, ζ * ζ ≠ 1 ∧
        ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace X, g v = ζ • v) ∨
      (Nat.card (movedGroup X) = 336 ∧ DMax p (movedGroup X) 4 ∧ p ≠ 7) ∨
      (Nat.card (movedGroup X) = 120 ∧ DMax p (movedGroup X) 5 ∧ p ≠ 5 ∧
        ∃ Q : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
          ∀ g ∈ X, IsIsom p Q g) ∨
      ∃ (f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
        (i₀ i₁ : Fin 3) (ζ : (ZMod p)ˣ), i₀ ≠ i₁ ∧
        (movedGroup X = gmmn p f i₀ i₁ ζ ∨ movedGroup X = g2mmn p f i₀ i₁ ζ)

end CFSG.StandardType.ZS

end
