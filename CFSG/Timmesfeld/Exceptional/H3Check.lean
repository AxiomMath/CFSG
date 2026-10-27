module

public import CFSG.Timmesfeld.Exceptional.H3Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.Exc.H3Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 120 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 360 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 120 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 360 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 120 6 360 fx fc fy (invLetter 3) ffi live 0 720 = true := by
  decide +kernel

theorem cover_all : coverOK 120 6 360 fx fc fy (invLetter 3) ffi live 0 720 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.Exc.H3Data
