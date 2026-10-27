module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSupport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def RT8 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
    v1Sub D.M V₀ V h.hyp151.isElemAbelian L = ⊥ →
    s15 D.M V₀ V h.hyp151.isElemAbelian L = 4 →
    3 ≤ gamma15 D.M V₀ V h.hyp151.isElemAbelian L →
    ∀ (g v : G), v ∈ conjSubgroup D.M g → v * v = 1 →
      (suppAct (wConjG D.M V₀ V h.hyp151.isElemAbelian L g) v).ncard ≤ 3 →
      (∀ E ∈ suppAct (wConjG D.M V₀ V h.hyp151.isElemAbelian L g) v,
        conjSubgroup E v = E ∧ E3.mQuot E (E ⊓ centralizer ({v} : Set G)) = 1) →
      ∀ a ∈ conjSubgroup V g, a * v * a⁻¹ * v⁻¹ ≠ 1 →
        centralizer ({a * v * a⁻¹ * v⁻¹} : Set G) ≤ conjSubgroup D.M g

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
