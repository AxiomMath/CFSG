module

public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.StandardType.ZS

variable {X : Type*} [Group X]

@[expose] def CoxeterConfig {ι : Type*} (E : Set X) (M : CoxeterMatrix ι) (d : ι → X) : Prop :=
  (∀ i, d i ∈ E) ∧ Function.Injective d ∧ (∀ i j, M i j = 3 → orderOf (d i * d j) = 3) ∧
    ∀ i j, i ≠ j → M i j = 2 → Commute (d i) (d j)

@[expose] def ScalarFrame (E : Set X) {k : ℕ} (d : Fin k → X) (e : X) : Prop :=
  (∀ i, d i ∈ E) ∧ Function.Injective d ∧ (Pairwise fun i j => Commute (d i) (d j)) ∧ e ∈ E ∧
    (∀ i, e ≠ d i) ∧ Commute e (List.ofFn d).prod

@[expose] def AffineTriangle (E : Set X) (a b c : X) : Prop :=
  a ∈ E ∧ b ∈ E ∧ c ∈ E ∧ orderOf (a * b) = 3 ∧ orderOf (a * c) = 3 ∧ orderOf (b * c) = 3 ∧
    orderOf (c * a * c * b) = 3

@[expose] def UnitaryFourConfig (E : Set X) (a b c d : X) : Prop :=
  a ∈ E ∧ b ∈ E ∧ c ∈ E ∧ d ∈ E ∧ orderOf (a * b) = 3 ∧ orderOf (a * c) = 3 ∧
    orderOf (a * d) = 3 ∧ orderOf (b * c) = 3 ∧ orderOf (c * d) = 3 ∧ orderOf (b * d) = 2 ∧
    orderOf (c * a * c * b) = 3 ∧ orderOf (c * a * c * d) = 3 ∧
    (orderOf (b * a * b * (d * c * d)) = 3 ∨ b * a * b = d * c * d)

end CFSG.StandardType.ZS
