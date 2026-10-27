module

public import CFSG.Walter.J1Recog.O1aData
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Walter.J1Recog.O1aData

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 1240 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 1240 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 3000 3000 =
      true := by
  decide +kernel

theorem facts_2 :
    factsOK 1240 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 6000 160 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 1240 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 0 6160 =
      true := by
  rw [show (6160 : ℕ) = 3000 + 3160 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (3160 : ℕ) = 3000 + 160 from rfl, factsOK_add, facts_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  exact facts_2

theorem cover_0 : coverOK 1240 10 6160 fx fc fy (invLetter 5) ffi live 0 12400 = true := by
  decide +kernel

theorem cover_all : coverOK 1240 10 6160 fx fc fy (invLetter 5) ffi live 0 12400 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 1240 = 1045 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Walter.J1Recog.O1aData
