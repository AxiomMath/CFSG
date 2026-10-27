module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.WreathBase
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72WreathL2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

structure TenHyp {G : Type} [Group G] [Finite G] {D : Set G} (hC : HypothesisC D)
    (f n : ℕ) : Prop where
  rad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥
  radH : CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha)
  two_le : 2 ≤ f
  five_le : 5 ≤ n
  iso : Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)

@[expose]
noncomputable def tenBase {G : Type} [Group G] {D : Set G} (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) :
    Subgroup G :=
  ((l2WreathBase f n).comap
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))))).map
    (Halpha D hC.alpha).subtype

@[expose] def TenSetupPerfect : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) (f n : ℕ),
    TenHyp hC f n →
    ∀ e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n,
      ⁅tenBase hC e, tenBase hC e⁆ = tenBase hC e

@[expose] def TenSetupQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) (f n : ℕ),
    TenHyp hC f n →
    CFSG.pCore 2 (Halpha D hC.alpha) = ⊥ ∨
      (f = 2 ∧ Nat.card (CFSG.pCore 2 (Halpha D hC.alpha)) = 2)

@[expose] def TenTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) (f n : ℕ),
    TenHyp hC f n →
    CFSG.pCore 2 (Halpha D hC.alpha) = ⊥ ∧ ¬ hC.alpha ⊆ (Halpha D hC.alpha : Set G)

@[expose] def TenThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) (f n : ℕ),
    TenHyp hC f n →
    ∀ e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n,
      ∀ β ∈ Dalpha D hC.alpha, ∀ v ∈ β,
        β = {x | ∃ l ∈ tenBase hC e, x = l * v * l⁻¹}

@[expose] def TenFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) (f n : ℕ),
    TenHyp hC f n →
    ∀ β ∈ Dalpha D hC.alpha,
      ⁅Subgroup.closure β, Subgroup.closure β⁆ ≠ ⊥ ∧
        ⁅Subgroup.closure β, Subgroup.closure β⁆ ≤ blockKernel hC.alpha

end CFSG.OddTranspositions.PartThree

end
