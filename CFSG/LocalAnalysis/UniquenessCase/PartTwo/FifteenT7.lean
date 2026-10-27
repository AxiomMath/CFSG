module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def RT7 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
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

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
