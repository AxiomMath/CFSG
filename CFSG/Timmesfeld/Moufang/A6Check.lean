module

public import CFSG.Timmesfeld.Moufang.A6Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.A6Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 1080 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 1080 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 3000 1320 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 1080 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 4320 =
      true := by
  rw [show (4320 : ℕ) = 3000 + 1320 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  exact facts_1

theorem cover_0 : coverOK 1080 8 4320 fx fc fy (invLetter 4) ffi live 0 8640 = true := by
  decide +kernel

theorem cover_all : coverOK 1080 8 4320 fx fc fy (invLetter 4) ffi live 0 8640 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 1080 = 1080 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.A6Data
