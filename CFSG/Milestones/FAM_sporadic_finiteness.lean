module

public import CFSG.Milestones.FAM_M_finiteness
public import CFSG.Sporadic.Presentation.All
public import CFSG.Sporadic.Bridge.Y322Central

public section

namespace CFSG.Milestones

theorem fam_sporadic_finiteness_tauCeti
    (G : Type) [Group G]
    (hrep : ∃ s : TauCeti.SporadicName, Nonempty (G ≃* s.Group)) : Finite G := by
  obtain ⟨s, ⟨e⟩⟩ := hrep
  have : Finite (Blueprint.NativeSporadic.Carrier .M) :=
    Sporadic.finite_carrier_M_of_card fam_m_finiteness
  obtain ⟨f⟩ := Sporadic.Bridge.Y443.nonempty_mulEquiv
  have : Finite TauCeti.SporadicName.M.Group := Finite.of_equiv _ f.toEquiv
  have := Sporadic.Presentation.finite_group_of this s
  exact Finite.of_equiv _ e.toEquiv.symm

end CFSG.Milestones

namespace CFSG.Milestones

theorem fam_sporadic_finiteness
    (G : Type) [Group G]
    (hrep : Blueprint.NativeSporadic.SporadicRep G) : Finite G :=
  Sporadic.finite_of_sporadicRep (Sporadic.finite_carrier_M_of_card fam_m_finiteness) hrep

end CFSG.Milestones
