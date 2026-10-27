module

public import CFSG.Timmesfeld.Bridge.RootStructW96DataA
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Bridge.WStarD4.DataA

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 98 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 390 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 98 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 390 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 98 8 390 fx fc fy (invLetter 4) ffi live 0 784 = true := by
  decide +kernel

theorem cover_all : coverOK 98 8 390 fx fc fy (invLetter 4) ffi live 0 784 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Bridge.WStarD4.DataA
