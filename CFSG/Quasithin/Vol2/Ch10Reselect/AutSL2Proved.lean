module

public import CFSG.Quasithin.Vol2.Ch10Reselect.AutSL2
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

theorem autSL2Exists : AutSL2Exists := by
  intro K _ _ _ _ α
  obtain ⟨M, σ, h⟩ := CFSG.RankThree.PartOne.KCRootAxis.exists_conj_mul_slFieldAut α
  refine ⟨M, σ, fun A => ?_⟩
  rw [h]
  rfl

end CFSG.Quasithin.Vol2.Ch10Reselect
