module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R15_6 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      ∀ g : G, V ≤ conjSubgroup D.M g → conjSubgroup V g ≤ D.M → ⁅V, conjSubgroup V g⁆ = ⊥

@[expose] def R15_8 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      E3.wClos V 0 D.M ≤ normalizer (wSub V₀ V h.hyp151.isElemAbelian L : Set G)

@[expose] def R15_9 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      E3.wClos V 0 D.M ≤ centralizer (V : Set G)

@[expose] def R15_11 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      ∀ i : ℕ, i ≤ 2 → ¬ centralizer (E3.cClos V i D.T : Set G) ≤ D.M →
        v1Sub D.M V₀ V h.hyp151.isElemAbelian L = ⊥ ∧
          ((gamma15 D.M V₀ V h.hyp151.isElemAbelian L = 2 ∧
              s15 D.M V₀ V h.hyp151.isElemAbelian L = 4 ∧ i = 2) ∨
            (s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 ∧
              gamma15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 3))

@[expose] def R15_12 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      ∀ n : ℕ, n ≤ 2 → n < gamma15 D.M V₀ V h.hyp151.isElemAbelian L →
        (calO n D.M V₀ V).Nonempty →
          gamma15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 3 ∧
            s15 D.M V₀ V h.hyp151.isElemAbelian L = 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
