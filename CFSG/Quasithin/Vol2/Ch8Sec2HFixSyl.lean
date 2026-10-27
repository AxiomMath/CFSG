module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFacts
public import CFSG.Quasithin.Background.HFixSylL3
public import CFSG.Quasithin.Background.HFixSylMathieu

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H.FixSyl

theorem hFixSylow82_holds : HFixSylow82 := by
  intro V _ _ H S h hSH hS
  rcases h with h | h | h | h
  · exact card_fixV_sylow_le_two_binaryNine h hSH hS
  · exact card_fixV_sylow_le_two_code22 h hSH hS
  · exact card_fixV_sylow_le_two_code24 h hSH hS
  · exact card_fixV_sylow_le_two_cocode24 h hSH hS

end CFSG.Quasithin.H13
