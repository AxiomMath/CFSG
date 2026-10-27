module

public import CFSG.Timmesfeld.RootInduction

public section

namespace CFSG.Timmesfeld

@[expose] def RootIHStruct (G : Type) [Group G] : Prop :=
  ∀ (G' : Type) [Group G'] (D' : Set G'), Hyp G' D' → Nat.card G' < Nat.card G →
    Outcome G' ∧ ((∃ d ∈ D', ∃ e ∈ rootSet D' d, e ≠ d) →
      RootClosure D' ∧ SpecialClosure D' ∧ RootMoufang D')

theorem RootIHStruct.rootIH {G : Type} [Group G] (h : RootIHStruct G) : RootIH G :=
  fun G' _ D' h' hlt => (h G' D' h' hlt).1

end CFSG.Timmesfeld
