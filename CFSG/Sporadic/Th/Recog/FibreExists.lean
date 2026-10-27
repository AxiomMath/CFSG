module

public import CFSG.Sporadic.Th.Recog.Orbit
public import CFSG.Sporadic.Th.Recog.Fibre

public section

namespace CFSG.Sporadic.Th.Recog

variable {G : Type} [Group G] [Finite G]

theorem exists_fibreData (S : ThSetting G) (hBB : A9FaithfulDimEight) : Nonempty (FibreData S) := by
  obtain ⟨σ, e, he⟩ := exists_iso_rho8a S hBB
  exact nonempty_fibreData_of_iso S he (q_eq_qf S he)

end CFSG.Sporadic.Th.Recog

end
