module

public import CFSG.Walter.J1Recog.O1bData
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Walter.J1Recog.O1bData

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 580 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 0 2040 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 580 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 0 2040 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 580 10 2040 fx fc fy (invLetter 5) ffi live 0 5800 = true := by
  decide +kernel

theorem cover_all : coverOK 580 10 2040 fx fc fy (invLetter 5) ffi live 0 5800 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 580 = 1 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Walter.J1Recog.O1bData
