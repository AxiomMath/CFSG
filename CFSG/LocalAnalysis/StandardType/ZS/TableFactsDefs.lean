module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMatrices

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable (p : ℕ) [Fact p.Prime]

@[expose] def TFNFourFive : Prop :=
  p = 5 → ∀ (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (X Y : Subgroup (U ≃ₗ[ZMod p] U)), Y ≤ X → ReflGen p X → QTwoLin.TransvectionFree X →
    SplitSupport X 4 → (ModelIso p .N4 (movedGroup X) ∨ ModelIso p .EN4 (movedGroup X)) →
    ReflGen p Y → SplitSupport Y 3 → ¬ IsOrthType p (movedGroup Y)

@[expose] def TFPrimCorankDim (l : ℕ) : Prop :=
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

@[expose] def TFDegenerateExtThree (l : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (X : Subgroup (W ≃ₗ[ZMod p] W)), p = 3 → 4 ≤ l → ReflGen p X →
    QTwoLin.TransvectionFree X → SplitSupport X l →
    (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    ∀ T ≤ X, (∀ s ∈ T, s ^ p = 1) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
      p ^ (l - 2) ≤ Nat.card T →
      (∀ s ∈ T, s ≠ 1 → Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace s) = 2) →
      ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) ∧ IsOrthType p (movedGroup X)

@[expose] def TFH3DataModel : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] (f : Module.Basis (Fin 4) (ZMod p) W)
    (α : ZMod p), p ≠ 2 → α ^ 2 = α + 1 → H3Data p (movedGroup (basisClosure f (h3Mats α)))

end CFSG.StandardType.ZS

end
