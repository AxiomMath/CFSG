module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSL3B
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompU3Five
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompU3Three
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompHatA6

public section

namespace CFSG.Quasithin.H13.S126C

theorem comp12626L3U3Odd_holds : Comp12626L3U3Odd := by
  intro Q _ K L P T v hQ h p hp hp2 hK
  rcases hK with hL3 | hU3
  · rcases h.eq_three_or_five_of_psl3 hQ hp hp2 hL3 with rfl | rfl
    · exact h.not_psl3_three hQ hL3
    · exact h.not_psl3_five hQ hL3
  · rcases h.eq_three_or_five_of_psu3 hQ hp hp2 hU3 with rfl | rfl
    · exact h.not_psu3_three hQ hU3
    · exact h.not_psu3_five hQ hU3

theorem comp12626CovOdd_holds : Comp12626CovOdd := by
  intro Q _ K L P T v hQ h hK
  rcases hK with ⟨s, p, hp, hp2, hs⟩ | hSU2 | hA6
  · cases s
    · rcases h.eq_three_or_five_of_su3 hQ hp hp2 hs with rfl | rfl
      · exact h.not_su3_three hQ hs
      · exact h.not_su3_five hQ hs
    · rcases h.eq_three_or_five_of_sl3 hQ hp hp2 hs with rfl | rfl
      · exact h.not_sl3_small hQ (Or.inl rfl) hs
      · exact h.not_sl3_small hQ (Or.inr rfl) hs
  · exact not_isSU3_two_of_isQuasisimple h.comp.1 hSU2
  · exact h.not_hatA6 hQ hA6

end CFSG.Quasithin.H13.S126C
