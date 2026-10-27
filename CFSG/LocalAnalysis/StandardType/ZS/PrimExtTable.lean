module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtLemmas
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMatrices
public import CFSG.LocalAnalysis.StandardType.ZS.TableCommon

public section

namespace CFSG.StandardType.ZS

@[expose] def PrimFrameData (p : ℕ) [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] (H : Subgroup (W ≃ₗ[ZMod p] W)) (h₁ z τ : W ≃ₗ[ZMod p] W) : Prop :=
  z ∈ H ∧ z * z = 1 ∧
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace z) + 2 =
      Module.finrank (ZMod p) W ∧
    h₁ ∈ H ∧ IsRefl p h₁ ∧ h₁ * z = z * h₁ ∧
    HardMathSupport.Kantor79.movedSpace h₁ ≤ HardMathSupport.Kantor79.movedSpace z ∧
    IsCaseCRefl p H z τ ∧ (∃ g ∈ H, τ = g * h₁ * g⁻¹) ∧
    ∀ x ∈ H, IsRefl p x →
      HardMathSupport.Kantor79.movedSpace x ≤ HardMathSupport.Kantor79.movedSpace z →
      ∃ g ∈ H, HardMathSupport.Kantor79.movedSpace (g * h₁ * g⁻¹) ≤
        HardMathSupport.Kantor79.movedSpace z ⊓ LinearMap.ker ((x : W →ₗ[ZMod p] W) - 1)

section TableFacts

variable (p : ℕ) [Fact p.Prime]

@[expose] def TFPrimCorankOne (l : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (X : Subgroup (W ≃ₗ[ZMod p] W)) (d : ℕ), p ≠ 2 → 3 ≤ l →
    Module.finrank (ZMod p) W = l + 1 → ReflGen p X → QTwoLin.TransvectionFree X →
    SplitSupport X l → ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) →
    ¬ IsOrthType p (movedGroup X) → (∀ z ∈ X, (∀ x ∈ X, z * x = x * z) → orderOf z ≤ 3) →
    DMax p X d → 3 < d →
    (l = 3 ∧ d = 5 ∧ p ≠ 5 ∧ ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W),
        α ^ 2 = α + 1 ∧ X = basisClosure f (h3Mats α)) ∨
      (l = 3 ∧ d = 4 ∧ p ≠ 7 ∧ ∃ (β : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W),
        2 * β ^ 2 + β + 1 = 0 ∧ X = basisClosure f (j34Mats β)) ∨
      (l = 4 ∧ d = 5 ∧ p ≠ 5 ∧ ∃ (α : ZMod p) (f : Module.Basis (Fin 5) (ZMod p) W),
        α ^ 2 = α + 1 ∧ X = basisClosure f (h4Mats α)) ∨
      (l = 4 ∧ d = 4 ∧ p ≠ 3 ∧ ∃ f : Module.Basis (Fin 5) (ZMod p) W,
        X = basisClosure f f4ExtMats)

@[expose] def TFDimThreeFive : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (F : Subgroup (W ≃ₗ[ZMod p] W)), 5 < p → Module.finrank (ZMod p) W = 4 → ReflGen p F →
    QTwoLin.TransvectionFree F → SplitSupport F 3 → DMax p F 5 → Nat.card F ≤ 120 →
    ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W), α ^ 2 = α + 1 ∧
      F = basisClosure f (h3Mats α)

@[expose] def TFH4Extend : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (B : Subgroup (W ≃ₗ[ZMod p] W)), 5 < p → ReflGen p B → QTwoLin.TransvectionFree B →
    SplitSupport B 4 → DMax p B 5 → (∀ z ∈ B, (∀ x ∈ B, z * x = x * z) → orderOf z ≤ 3) →
    ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, IsRefl p x → IsRefl p y → IsRefl p z →
      orderOf (x * y) = 5 → orderOf (y * z) = 3 → orderOf (x * z) = 2 →
      ∃ w ∈ B, IsRefl p w ∧ orderOf (w * x) = 2 ∧ orderOf (w * z) = 3

@[expose] def TFH3Model : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] (f : Module.Basis (Fin 4) (ZMod p) W)
    (α : ZMod p), p ≠ 2 → p ≠ 5 → α ^ 2 = α + 1 →
    Nat.card (basisClosure f (h3Mats α)) = 120 ∧
    (∀ h₁ z τ : W ≃ₗ[ZMod p] W, LinearMap.toMatrix f f (h₁ : W →ₗ[ZMod p] W) = diagSignMat 0 →
      LinearMap.toMatrix f f (z : W →ₗ[ZMod p] W) = diagSignMat 0 * diagSignMat 1 →
      LinearMap.toMatrix f f (τ : W →ₗ[ZMod p] W) = diagSignMat 2 →
      PrimFrameData p (basisClosure f (h3Mats α)) h₁ z τ) ∧
    ∀ a ∈ basisClosure f (h3Mats α), ∀ b ∈ basisClosure f (h3Mats α),
      ∀ c ∈ basisClosure f (h3Mats α), IsRefl p a → IsRefl p b → IsRefl p c →
      orderOf (a * b) = 5 → c ∉ Subgroup.closure {a, b} →
      ∃ g ∈ Subgroup.closure {a, b}, g * c * g⁻¹ * a = a * (g * c * g⁻¹)

@[expose] def TFH3Pair : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] (f : Module.Basis (Fin 4) (ZMod p) W)
    (α : ZMod p), p ≠ 2 → p ≠ 5 → α ^ 2 = α + 1 →
    ∀ h₁ a : W ≃ₗ[ZMod p] W, LinearMap.toMatrix f f (h₁ : W →ₗ[ZMod p] W) = diagSignMat 0 →
      LinearMap.toMatrix f f (a : W →ₗ[ZMod p] W) = Matrix.blockSucc (h3BlockMat α) →
      ∀ g ∈ basisClosure f (h3Mats α), IsRefl p g →
        HardMathSupport.Kantor79.movedSpace g ≤
          HardMathSupport.Kantor79.movedSpace h₁ ⊔ HardMathSupport.Kantor79.movedSpace a →
        g ∈ Subgroup.closure {h₁, a}

@[expose] def TFJ34Model : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] (f : Module.Basis (Fin 4) (ZMod p) W)
    (β : ZMod p), p ≠ 2 → p ≠ 7 → 2 * β ^ 2 + β + 1 = 0 →
    ∀ h₁ z τ : W ≃ₗ[ZMod p] W, LinearMap.toMatrix f f (h₁ : W →ₗ[ZMod p] W) = diagSignMat 0 →
      LinearMap.toMatrix f f (z : W →ₗ[ZMod p] W) = diagSignMat 0 * diagSignMat 1 →
      LinearMap.toMatrix f f (τ : W →ₗ[ZMod p] W) = diagSignMat 2 →
      PrimFrameData p (basisClosure f (j34Mats β)) h₁ z τ

@[expose] def TFF4Model : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] (f : Module.Basis (Fin 5) (ZMod p) W),
    p ≠ 2 → p ≠ 3 →
    ∀ h₁ z τ : W ≃ₗ[ZMod p] W, LinearMap.toMatrix f f (h₁ : W →ₗ[ZMod p] W) = diagSignMat 0 →
      LinearMap.toMatrix f f (z : W →ₗ[ZMod p] W) =
        diagSignMat 0 * diagSignMat 1 * diagSignMat 2 →
      LinearMap.toMatrix f f (τ : W →ₗ[ZMod p] W) = diagSignMat 3 →
      PrimFrameData p (basisClosure f f4ExtMats) h₁ z τ

@[expose] def TFH4Model5 : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] (f : Module.Basis (Fin 5) (ZMod p) W)
    (α : ZMod p), p ≠ 2 → p ≠ 5 → α ^ 2 = α + 1 →
    ∀ h₁ z τ : W ≃ₗ[ZMod p] W, LinearMap.toMatrix f f (h₁ : W →ₗ[ZMod p] W) = diagSignMat 0 →
      LinearMap.toMatrix f f (z : W →ₗ[ZMod p] W) =
        diagSignMat 0 * diagSignMat 1 * diagSignMat 2 →
      LinearMap.toMatrix f f (τ : W →ₗ[ZMod p] W) = diagSignMat 3 →
      PrimFrameData p (basisClosure f (h4Mats α)) h₁ z τ ∧
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p (basisClosure f (h4Mats α))
          (LinearMap.ker ((h₁ : W →ₗ[ZMod p] W) - 1)))) + 2 = 5 ∧
      IrredOnSection (reflSubgroupIn p (basisClosure f (h4Mats α))
          (LinearMap.ker ((h₁ : W →ₗ[ZMod p] W) - 1))) ⊥
        (HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p (basisClosure f (h4Mats α))
          (LinearMap.ker ((h₁ : W →ₗ[ZMod p] W) - 1))))

@[expose] def TFH4Model : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] (f : Module.Basis (Fin 4) (ZMod p) W)
    (α : ZMod p), p ≠ 2 → p ≠ 5 → α ^ 2 = α + 1 →
    OneClass p (basisClosure f (h4BlockMats α)) ∧
    IrredOnSection (basisClosure f (h4BlockMats α)) ⊥ ⊤ ∧
    SplitSupport (fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0)) 3 ∧
    HardMathSupport.Kantor79.commutatorSpace
        (fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0)) =
      LinearMap.ker (f.coord 0) ∧
    centralizerSpace (fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0)) =
      Submodule.span (ZMod p) {f 0} ∧
    Nat.card (fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0)) = 120 ∧
    DMax p (fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0)) 5

end TableFacts

end CFSG.StandardType.ZS

end
