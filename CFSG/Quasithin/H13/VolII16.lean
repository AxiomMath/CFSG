module

public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
public import CFSG.Quasithin.H13.VolIAltCoverSeven
public import CFSG.Quasithin.H13.VolII16A7Four
public import CFSG.Quasithin.H13.VolII16Scalar
public import CFSG.Quasithin.H13.VolII16SL3
public import CFSG.Quasithin.H13.VolII16Wedge
public import CFSG.Quasithin.Background.B5Inputs

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin

theorem asI16Cover328_holds :
    H13.AsI16Cover328 := by
  intro V _ _ hV2 L hI
  refine ⟨fun h => ?_, binaryNaturalSL_three_card_le hV2 hI⟩
  rcases h with h | h | ⟨n, hn, h⟩ | h | h | h | h | h
  · exact eq_bot_of_restrict (FFModel.altDn 5) altNaturalCoverFive_holds hV2 hI h
  · exact eq_bot_of_restrict (FFModel.altDn 7) altNaturalCoverSeven_holds hV2 hI h
  · exact binaryNaturalSL_three_eq_bot hV2 hI hn h
  · exact binaryNaturalSL_four_eq_bot hV2 hI h
  · exact binaryNaturalSL_five_eq_bot hV2 hI h
  · exact sLExteriorTwo_five_eq_bot hV2 hI h
  · exact a7Four_eq_bot hV2 hI h
  · exact tripleA6Six_eq_bot hV2 hI h

theorem asI16Cover_holds : AsI16Cover := by
  intro V _ _ hV2 L hI h
  rcases h with ⟨n, hn, h⟩ | h | h
  · exact binaryNaturalSL_three_eq_bot hV2 hI hn h
  · exact binaryNaturalSL_four_eq_bot hV2 hI h
  · exact binaryNaturalSL_five_eq_bot hV2 hI h

end CFSG.Quasithin.H13.VolI
