module

public import CFSG.Timmesfeld.Exceptional.TwoLinesData168
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.TwoLines.Data168

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 2027 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 2027 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 3000 3000 =
      true := by
  decide +kernel

theorem facts_2 :
    factsOK 2027 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 6000 256 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 2027 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 6256 =
      true := by
  rw [show (6256 : ℕ) = 3000 + 3256 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (3256 : ℕ) = 3000 + 256 from rfl, factsOK_add, facts_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  exact facts_2

theorem cover_0 : coverOK 2027 6 6256 fx fc fy (invLetter 3) ffi live 0 12162 = true := by
  decide +kernel

theorem cover_all : coverOK 2027 6 6256 fx fc fy (invLetter 3) ffi live 0 12162 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.TwoLines.Data168
