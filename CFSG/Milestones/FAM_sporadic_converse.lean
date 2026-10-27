module

public import CFSG.Milestones.FAM_M_finiteness
public import CFSG.Milestones.FAM_M_simplicity
public import CFSG.Sporadic.Bridge.Converse

public section

universe u v w

namespace CFSG.Open.Milestones

open Assembly in
theorem _root_.CFSG.Milestones.fam_sporadic_converse_tauCeti
    (s : TauCeti.SporadicName) :
    Finite s.Group ∧ IsSimpleGroup s.Group := by
  exact CFSG.Sporadic.Bridge.tauCeti_finite_simple CFSG.Milestones.fam_m_finiteness
    CFSG.Milestones.fam_m_simplicity s

end CFSG.Open.Milestones

namespace CFSG.Milestones

theorem fam_sporadic_converse
    (G : Type) [Group G]
    (hrep : Blueprint.NativeSporadic.SporadicRep G) : Finite G ∧ IsSimpleGroup G := by
  exact Sporadic.Bridge.finite_simple_of_sporadicRep fam_m_finiteness fam_m_simplicity G hrep

end CFSG.Milestones
