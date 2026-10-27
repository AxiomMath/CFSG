module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Milestones

theorem fam_sporadic_representatives_definition (G : Type) [Group G] :
    Blueprint.NativeSporadic.SporadicRep G ↔
      ∃ s : TauCeti.SporadicName, Nonempty (G ≃* Blueprint.NativeSporadic.Carrier s) := Iff.rfl

end CFSG.Milestones
