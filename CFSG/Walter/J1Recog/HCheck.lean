module

public import CFSG.Walter.J1Recog.HData
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Walter.J1Recog.HData

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 168 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 504 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 168 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 504 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 168 6 504 fx fc fy (invLetter 3) ffi live 0 1008 = true := by
  decide +kernel

theorem cover_all : coverOK 168 6 504 fx fc fy (invLetter 3) ffi live 0 1008 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 168 = 168 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Walter.J1Recog.HData
