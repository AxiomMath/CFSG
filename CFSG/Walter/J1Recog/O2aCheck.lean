module

public import CFSG.Walter.J1Recog.O2aData
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Walter.J1Recog.O2aData

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 204 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 0 766 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 204 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 0 766 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 204 10 766 fx fc fy (invLetter 5) ffi live 0 2040 = true := by
  decide +kernel

theorem cover_all : coverOK 204 10 766 fx fc fy (invLetter 5) ffi live 0 2040 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 204 = 1 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Walter.J1Recog.O2aData
