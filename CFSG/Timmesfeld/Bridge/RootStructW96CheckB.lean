module

public import CFSG.Timmesfeld.Bridge.RootStructW96DataB
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Bridge.WStarD4.DataB

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 96 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 384 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 96 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 384 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 96 8 384 fx fc fy (invLetter 4) ffi live 0 768 = true := by
  decide +kernel

theorem cover_all : coverOK 96 8 384 fx fc fy (invLetter 4) ffi live 0 768 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Bridge.WStarD4.DataB
