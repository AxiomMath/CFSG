module

public import CFSG.Walter.J1Recog.O2bData
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Walter.J1Recog.O2bData

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 1515 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 1515 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 3000 2074 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 1515 11 fx fc fy kind wi fs ft fo refs pl (invLetter 5)
      words [[0], [2], [4]] 0 5074 =
      true := by
  rw [show (5074 : ℕ) = 3000 + 2074 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  exact facts_1

theorem cover_0 : coverOK 1515 10 5074 fx fc fy (invLetter 5) ffi live 0 15150 = true := by
  decide +kernel

theorem cover_all : coverOK 1515 10 5074 fx fc fy (invLetter 5) ffi live 0 15150 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 1515 = 1 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Walter.J1Recog.O2bData
