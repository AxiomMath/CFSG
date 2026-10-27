module

public import CFSG.Timmesfeld.Exceptional.SigmaFarDataK24
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.SigmaFar.DataK24

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 24 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 0 72 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 24 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 0 72 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 24 6 72 fx fc fy (invLetter 3) ffi live 0 144 = true := by
  decide +kernel

theorem cover_all : coverOK 24 6 72 fx fc fy (invLetter 3) ffi live 0 144 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 24 = 24 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.SigmaFar.DataK24
