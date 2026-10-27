module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerOps
public import CFSG.RankThree.PartOne.K159.KleinModel
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def SL4HomW1Statement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    (∀ f : (Fin 4 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 4 → K),
      (∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v : Fin 4 → K) (w : Fin 3 ⊕ Fin 3 → K),
        f (A • v) (PartOne.K159.Klein.rho A w) = A • f v w) → f = 0) ∧
    ∀ f : (Fin 4 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 4 → K),
      (∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v : Fin 4 → K) (w : Fin 3 ⊕ Fin 3 → K),
        f (Matrix.SpecialLinearGroup.transpose A⁻¹ • v) (PartOne.K159.Klein.rho A w) =
          Matrix.SpecialLinearGroup.transpose A⁻¹ • f v w) → f = 0

@[expose] def SL4HomW2Statement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ σ : K ≃+* K,
    ∀ f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K),
      (∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v u : Fin 4 → K),
        f (Matrix.SpecialLinearGroup.map (σ : K →+* K) A • v)
            (Matrix.SpecialLinearGroup.transpose A⁻¹ • u) =
          PartOne.K159.Klein.rho A (f v u)) → f = 0

@[expose] def SL4HomW3Statement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ σ : K ≃+* K,
    ∀ f : (Fin 4 → K) →ₗ[K] Module.End K (Fin 3 ⊕ Fin 3 → K),
      (∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v : Fin 4 → K), ∃ c : K,
        f (Matrix.SpecialLinearGroup.map (σ : K →+* K) A • v) =
          (PartOne.K159.Klein.rho A).toLinearMap ∘ₗ f v ∘ₗ
            (PartOne.K159.Klein.rho A⁻¹).toLinearMap + c • LinearMap.id) →
      ∀ v : Fin 4 → K, ∃ c : K, f v = c • LinearMap.id

@[expose] def SL4NoInvFormStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ σ : K ≃+* K,
    ∀ β : (Fin 4 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 4 → K) →ₗ[K]
        (Fin 3 ⊕ Fin 3 → K) →ₗ[K] K,
      (∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v v' : Fin 4 → K)
          (w w' : Fin 3 ⊕ Fin 3 → K),
        β (Matrix.SpecialLinearGroup.map (σ : K →+* K) A • v) (PartOne.K159.Klein.rho A w)
            (Matrix.SpecialLinearGroup.map (σ : K →+* K) A • v') (PartOne.K159.Klein.rho A w') =
          β v w v' w') → β = 0

section Layers

@[expose] def Sec717NbarKStructureStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ (m : ℕ) (γ : G → GaloisField 2 m) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 m) γ),
      GlobalModelData M Q Z γ M₀ →
      ∀ (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[GaloisField 2 m] M₀.E)),
        (∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
          x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
            φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x)) →
        ∀ T : Submodule (GaloisField 2 m) M₀.E,
          (∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
            LinearMap.range (opm (φ a)) = T) →
          ∀ g ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ c : GaloisField 2 m,
            ∃ g' ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
              IsLayerCorner T (M₀.B.orthogonal T) (opm (φ g') - c • opm (φ g))

@[expose] def Sec717LTypingStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    ∀ (m : ℕ) (γ : G → GaloisField 2 m) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 m) γ),
      GlobalModelData M Q Z γ M₀ →
      ∀ (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[GaloisField 2 m] M₀.E)),
        (∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
          x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
            φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x)) →
          ∃ η : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) →*
              Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 m),
            Function.Surjective η ∧
            (∀ r, η r = 1 ↔
              (r : ↥(bar M Q (H0 M Z))) ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) ∧
            ∃ θ : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z))) →*
                Multiplicative (Fin 4 → GaloisField 2 m),
              Function.Surjective θ ∧
              (∀ l, θ l = 1 ↔
                (l : ↥(bar M Q (H0 M Z))) ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ∧
              ∀ (r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))))
                (l l' : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z)))),
                (l' : ↥(bar M Q (H0 M Z))) =
                    (r : ↥(bar M Q (H0 M Z))) * l * (r : ↥(bar M Q (H0 M Z)))⁻¹ →
                  Multiplicative.toAdd (θ l') = η r • Multiplicative.toAdd (θ l)

@[expose] def Sec717LayerWedgeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    ∀ (m : ℕ) (γ : G → GaloisField 2 m) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 m) γ),
      GlobalModelData M Q Z γ M₀ →
      ∀ (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[GaloisField 2 m] M₀.E)),
        (∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
          x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
            φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x)) →
        ∀ T : Submodule (GaloisField 2 m) M₀.E,
          (∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
            LinearMap.range (opm (φ a)) = T) →
          ∃ η : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) →*
              Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 m),
            Function.Surjective η ∧
            (∀ r, η r = 1 ↔
              (r : ↥(bar M Q (H0 M Z))) ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) ∧
            (∃ θ : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z))) →*
                Multiplicative (Fin 4 → GaloisField 2 m),
              Function.Surjective θ ∧
              (∀ l, θ l = 1 ↔
                (l : ↥(bar M Q (H0 M Z))) ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ∧
              ∀ (r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))))
                (l l' : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z)))),
                (l' : ↥(bar M Q (H0 M Z))) =
                    (r : ↥(bar M Q (H0 M Z))) * l * (r : ↥(bar M Q (H0 M Z)))⁻¹ →
                  Multiplicative.toAdd (θ l') = η r • Multiplicative.toAdd (θ l)) ∧
            ∃ ψ : ↥T ≃ₗ[GaloisField 2 m] (Fin 3 ⊕ Fin 3 → GaloisField 2 m),
              ∀ (r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))) (w w' : ↥T),
                (w' : M₀.E) = φ (r : ↥(bar M Q (H0 M Z))) w →
                  ψ w' = PartOne.K159.Klein.rho (η r) (ψ w)

end Layers

end CFSG.RankThree.GF2n.Stroth80
