module

public import CFSG.Timmesfeld.Moufang.J2Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.J2Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 560 15 fx fc fy kind wi fs ft fo refs pl (invLetter 7)
      words [[0], [2], [4], [6]] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 560 15 fx fc fy kind wi fs ft fo refs pl (invLetter 7)
      words [[0], [2], [4], [6]] 3000 920 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 560 15 fx fc fy kind wi fs ft fo refs pl (invLetter 7)
      words [[0], [2], [4], [6]] 0 3920 =
      true := by
  rw [show (3920 : ℕ) = 3000 + 920 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  exact facts_1

theorem cover_0 : coverOK 560 14 3920 fx fc fy (invLetter 7) ffi live 0 7840 = true := by
  decide +kernel

theorem cover_all : coverOK 560 14 3920 fx fc fy (invLetter 7) ffi live 0 7840 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 560 = 560 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.J2Data
