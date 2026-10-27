module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R15_3Small (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp151 D V₀ V L), mSub V₀ ≤ 2 →
    (∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L)) →
      Desc153 D V₀ V h.isElemAbelian L

@[expose] def RT7Small (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L), mSub V₀ ≤ 2 →
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      ∀ (g : G) (X : Subgroup G), X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L →
        ∀ F C K : Subgroup G, IsElemAbelian 2 F → F ≤ conjSubgroup D.M g → C ≤ F →
          F ≤ normalizer
            ((conjSubgroup (X ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g : Subgroup G) : Set G) →
          (∀ x ∈ F, x ∈ C ↔ ∀ d ∈ conjSubgroup (X ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g,
            x * d * x⁻¹ * d⁻¹ ∈ conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g) →
          conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g ≤ K →
          K ≤ conjSubgroup (X ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g →
          E3.mQuot (conjSubgroup (X ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g) K = 1 →
          (∀ x ∈ F, ∀ k ∈ K,
            x * k * x⁻¹ * k⁻¹ ∈ conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g) →
          2 ≤ E3.mQuot F C →
            gamma15 D.M V₀ V h.hyp151.isElemAbelian L = 3 ∧
              s15 D.M V₀ V h.hyp151.isElemAbelian L = 2

@[expose] def R15_6Small (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L), mSub V₀ ≤ 2 →
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      ∀ g : G, V ≤ conjSubgroup D.M g → conjSubgroup V g ≤ D.M → ⁅V, conjSubgroup V g⁆ = ⊥

@[expose] def R15_8Small (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L), mSub V₀ ≤ 2 →
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      E3.wClos V 0 D.M ≤ normalizer (wSub V₀ V h.hyp151.isElemAbelian L : Set G)

@[expose] def R15_9Small (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L), mSub V₀ ≤ 2 →
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      E3.wClos V 0 D.M ≤ centralizer (V : Set G)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
