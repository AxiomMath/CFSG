module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def U3Fix3Inner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSU3 X 3 → ∀ α : MulAut X, α ^ 7 = 1 →
    α ∈ (MulAut.conj : X →* MulAut X).range → ∃ z : X, orderOf z = 3 ∧ α z = z

@[expose] def U3Fix3Field : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSU3 X 21 → ∀ α : MulAut X, α ^ 7 = 1 →
    α ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ ∀ e ∈ E, α e = e

@[expose] def U3E9Cover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSU3 X 3 → ∀ z : X, orderOf z = 3 →
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ z ∈ E

@[expose] def U3E9Fix : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSU3 X 3 → ∀ x : X, orderOf x = 7 → ∀ β : MulAut X, β ^ 3 = 1 → β x = x →
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ ∀ e ∈ E, β e = e

end CFSG.LocalAnalysis.UniquenessCase.UCK
