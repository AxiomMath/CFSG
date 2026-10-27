module

public import CFSG.Timmesfeld.Exceptional.TwoLinesData1080
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.TwoLines.Data1080

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 3218 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 3218 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 3000 3000 =
      true := by
  decide +kernel

theorem facts_2 :
    factsOK 3218 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 6000 3000 =
      true := by
  decide +kernel

theorem facts_3 :
    factsOK 3218 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 9000 1305 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 3218 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 10305 =
      true := by
  rw [show (10305 : ℕ) = 3000 + 7305 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (7305 : ℕ) = 3000 + 4305 from rfl, factsOK_add, facts_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  rw [show (4305 : ℕ) = 3000 + 1305 from rfl, factsOK_add, facts_2,
    Bool.true_and, show (6000 : ℕ) + 3000 = 9000 from rfl]
  exact facts_3

theorem cover_0 : coverOK 3218 6 10305 fx fc fy (invLetter 3) ffi live 0 19308 = true := by
  decide +kernel

theorem cover_all : coverOK 3218 6 10305 fx fc fy (invLetter 3) ffi live 0 19308 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.TwoLines.Data1080
