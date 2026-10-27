module

public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.BenderSuzuki

@[expose] def PSL2SylowCoordStmt : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (L : Type) [Group L], Nonempty (L ≃* PSL2Model n) →
    ∀ P : Sylow 2 L, ∃ φ : L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      (P : Subgroup L).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n)

@[expose] def L2TorusIrredStmt : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [CharP F 2], 4 ≤ Fintype.card F →
    ∀ x a b h : Matrix.SpecialLinearGroup (Fin 2) F, a ∈ upperUnipotent F →
      b ∈ upperUnipotent F → a ≠ 1 → b ≠ 1 → a ≠ b → x * x = 1 → orderOf (a * x) = 3 →
      Subgroup.closure {x, a, b} = ⊤ → h * a * h⁻¹ = b →
      ∀ W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), W ≤ upperUnipotent F → a ∈ W →
        (∀ w ∈ W, h * w * h⁻¹ ∈ W) → W = upperUnipotent F

@[expose] def NaturalComplementStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Fintype F] [CharP F 2],
    4 ≤ Fintype.card F → ∀ (X : Subgroup G) (φ : ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F)
      (θ : (Fin 2 → F) → G), ARS.IsNaturalModule φ θ →
      (∀ v, θ v ∈ X → v = 0) → (∀ g : G, ∃ v, ∃ y ∈ X, g = θ v * y) →
      ∀ x a b : G, x * x = 1 → a * a = 1 → b * b = 1 → (∀ v, θ v ≠ x) → (∀ v, θ v ≠ a) →
        (∀ v, θ v ≠ b) → (∀ g : G, ∃ v, ∃ k ∈ Subgroup.closure {x, a, b}, g = θ v * k) →
        ∀ v, θ v ∈ Subgroup.closure {x, a, b} → v = 0

end CFSG.Timmesfeld.Bridge.RootClosure
