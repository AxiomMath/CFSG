module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4TitsB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutLie

public section

namespace CFSG.Quasithin.H23P4


theorem rowTits_of_isTits {X : Type} [Group X] [Finite X] (h : IsTits X) : RowTits X := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 h
  exact ⟨center_eq_bot_transport e CFSG.Sporadic.Schreier.Tits.titsD_center,
    CFSG.Quasithin.H23Out.out5Pow_of_isTits h, CenOvergroup.of_mulEquiv e cenOvergroup_titsD⟩

end CFSG.Quasithin.H23P4
