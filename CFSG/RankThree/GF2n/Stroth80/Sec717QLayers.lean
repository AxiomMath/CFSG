module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveOpm
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Sec717QLayersStatement : Prop :=
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
        (∀ l₁ ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
          ∀ l₂ ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
            ∀ x y : M₀.E, M₀.B (opm (φ l₁) x) (opm (φ l₂) y) = 0) ∧
        ∀ l ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)), ∀ c : GaloisField 2 m,
          ∃ l' ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)), opm (φ l') = c • opm (φ l)

end CFSG.RankThree.GF2n.Stroth80
