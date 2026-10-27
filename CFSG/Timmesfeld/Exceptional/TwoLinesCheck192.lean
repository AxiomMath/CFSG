module

public import CFSG.Timmesfeld.Exceptional.TwoLinesData192
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.TwoLines.Data192

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 192 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 576 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 192 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 576 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 192 6 576 fx fc fy (invLetter 3) ffi live 0 1152 = true := by
  decide +kernel

theorem cover_all : coverOK 192 6 576 fx fc fy (invLetter 3) ffi live 0 1152 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.TwoLines.Data192
