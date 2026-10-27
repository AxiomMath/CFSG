module

public import CFSG.Timmesfeld.Exceptional.L211Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.Exc.L211Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 660 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 1980 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 660 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 1980 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 660 6 1980 fx fc fy (invLetter 3) ffi live 0 3960 = true := by
  decide +kernel

theorem cover_all : coverOK 660 6 1980 fx fc fy (invLetter 3) ffi live 0 3960 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.Exc.L211Data
