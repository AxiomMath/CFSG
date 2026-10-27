module

public import CFSG.Timmesfeld.Exceptional.SigmaFarDataTriv
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.SigmaFar.DataTriv

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 3787 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 3787 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 3000 3000 =
      true := by
  decide +kernel

theorem facts_2 :
    factsOK 3787 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 6000 3000 =
      true := by
  decide +kernel

theorem facts_3 :
    factsOK 3787 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 9000 2313 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 3787 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 0 11313 =
      true := by
  rw [show (11313 : ℕ) = 3000 + 8313 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (8313 : ℕ) = 3000 + 5313 from rfl, factsOK_add, facts_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  rw [show (5313 : ℕ) = 3000 + 2313 from rfl, factsOK_add, facts_2,
    Bool.true_and, show (6000 : ℕ) + 3000 = 9000 from rfl]
  exact facts_3

theorem cover_0 : coverOK 3787 6 11313 fx fc fy (invLetter 3) ffi live 0 20000 = true := by
  decide +kernel

theorem cover_1 : coverOK 3787 6 11313 fx fc fy (invLetter 3) ffi live 20000 2722 = true := by
  decide +kernel

theorem cover_all : coverOK 3787 6 11313 fx fc fy (invLetter 3) ffi live 0 22722 = true := by
  rw [show (22722 : ℕ) = 20000 + 2722 from rfl, coverOK_add, cover_0,
    Bool.true_and, show (0 : ℕ) + 20000 = 20000 from rfl]
  exact cover_1

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.SigmaFar.DataTriv
