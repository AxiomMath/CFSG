module

public import CFSG.Timmesfeld.Exceptional.TwoLinesDataTriv
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.TwoLines.DataTriv

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 109 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 394 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 109 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 394 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 109 6 394 fx fc fy (invLetter 3) ffi live 0 654 = true := by
  decide +kernel

theorem cover_all : coverOK 109 6 394 fx fc fy (invLetter 3) ffi live 0 654 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.TwoLines.DataTriv
