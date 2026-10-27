module

public import Mathlib.Data.Finset.Defs

public section

namespace CFSG.Decide.Bounded

scoped instance (priority := high) decidableBAllList {α : Type*} (p : α → Prop)
    [DecidablePred p] (l : List α) : Decidable (∀ x, x ∈ l → p x) :=
  List.decidableBAll p l

scoped instance (priority := high) decidableBExList {α : Type*} (p : α → Prop)
    [DecidablePred p] (l : List α) : Decidable (∃ x, x ∈ l ∧ p x) :=
  List.decidableBEx p l

scoped instance (priority := high) decidableBAllFinset {α : Type*} {s : Finset α}
    {p : ∀ a ∈ s, Prop} [∀ a (h : a ∈ s), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ s), p a h) :=
  Finset.decidableDforallFinset

end CFSG.Decide.Bounded
