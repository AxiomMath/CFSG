module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.PartTwo.Sec4.Item47Native

public section

namespace CFSG.Quasithin.H23Out

section J2


theorem noFiveOut_of_isSporadic_J2 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .J2 X) : NoFiveOut X := by
  obtain ⟨e⟩ := h
  exact NoFiveOut.of_equiv_card_outer_le e
    (CFSG.RankThree.PartTwo.Sec4.card_outer_J2.trans (by norm_num))

theorem out5Pow_of_isSporadic_J2 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .J2 X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isSporadic_J2 h)

end J2

section HS


theorem noFiveOut_of_isSporadic_HS {X : Type} [Group X] [Finite X]
    (h : IsSporadic .HS X) : NoFiveOut X := by
  obtain ⟨e⟩ := h
  exact NoFiveOut.of_equiv_card_outer_le e
    (CFSG.RankThree.PartTwo.Sec4.card_outer_HS.trans (by norm_num))

theorem out5Pow_of_isSporadic_HS {X : Type} [Group X] [Finite X]
    (h : IsSporadic .HS X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isSporadic_HS h)

end HS

section Ru


theorem noFiveOut_of_isSporadic_Ru {X : Type} [Group X] [Finite X]
    (h : IsSporadic .Ru X) : NoFiveOut X := by
  obtain ⟨e⟩ := h
  exact NoFiveOut.of_equiv_card_outer_le e
    (CFSG.RankThree.PartTwo.Sec4.card_outer_Ru.trans (by norm_num))

theorem out5Pow_of_isSporadic_Ru {X : Type} [Group X] [Finite X]
    (h : IsSporadic .Ru X) : Out5Pow X :=
  Out5Pow.of_noFiveOut (noFiveOut_of_isSporadic_Ru h)

end Ru

end CFSG.Quasithin.H23Out
