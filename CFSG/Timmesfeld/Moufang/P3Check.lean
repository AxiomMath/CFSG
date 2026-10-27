module

public import CFSG.Timmesfeld.Moufang.P3Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.P3Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 1120 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4], [6]] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 1120 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4], [6]] 3000 2600 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 1120 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4], [6]] 0 5600 =
      true := by
  rw [show (5600 : ℕ) = 3000 + 2600 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  exact facts_1

theorem cover_0 : coverOK 1120 10 5600 fx fc fy (invLetter 5) ffi live 0 11200 = true := by
  decide +kernel

theorem cover_all : coverOK 1120 10 5600 fx fc fy (invLetter 5) ffi live 0 11200 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 1120 = 1120 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.P3Data
