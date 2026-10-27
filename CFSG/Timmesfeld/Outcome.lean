module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def Outcome (G : Type) [Group G] : Prop :=
  (∃ n f : ℕ, 3 ≤ n ∧ 1 ≤ f ∧ LieModel G .PSL n 2 f) ∨
  (∃ n f : ℕ, 3 ≤ n ∧ 1 ≤ f ∧ LieModel G .PSp n 2 f) ∨
  (∃ n f : ℕ, 4 ≤ n ∧ 1 ≤ f ∧ (LieModel G .POmegaPlus n 2 f ∨ LieModel G .POmegaMinus n 2 f)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ LieModel G .G2 0 2 f) ∨
  (∃ f : ℕ, 1 ≤ f ∧ ∃ t ∈ ({.trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag),
      LieModel G t 0 2 f) ∨
  LieModel G .PSU 3 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
    NativeSporadic.IsSporadic G .J2

end CFSG.Timmesfeld
