module

public import CFSG.Timmesfeld.Exceptional.SigmaFarData7560
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Moufang.SigmaFar.Data7560

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 7585 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 7585 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 3000 3000 =
      true := by
  decide +kernel

theorem facts_2 :
    factsOK 7585 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 6000 3000 =
      true := by
  decide +kernel

theorem facts_3 :
    factsOK 7585 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 9000 3000 =
      true := by
  decide +kernel

theorem facts_4 :
    factsOK 7585 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 12000 3000 =
      true := by
  decide +kernel

theorem facts_5 :
    factsOK 7585 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 15000 3000 =
      true := by
  decide +kernel

theorem facts_6 :
    factsOK 7585 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 18000 3000 =
      true := by
  decide +kernel

theorem facts_7 :
    factsOK 7585 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 21000 1760 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 7585 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words subs 0 22760 =
      true := by
  rw [show (22760 : ℕ) = 3000 + 19760 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (19760 : ℕ) = 3000 + 16760 from rfl, factsOK_add, facts_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  rw [show (16760 : ℕ) = 3000 + 13760 from rfl, factsOK_add, facts_2,
    Bool.true_and, show (6000 : ℕ) + 3000 = 9000 from rfl]
  rw [show (13760 : ℕ) = 3000 + 10760 from rfl, factsOK_add, facts_3,
    Bool.true_and, show (9000 : ℕ) + 3000 = 12000 from rfl]
  rw [show (10760 : ℕ) = 3000 + 7760 from rfl, factsOK_add, facts_4,
    Bool.true_and, show (12000 : ℕ) + 3000 = 15000 from rfl]
  rw [show (7760 : ℕ) = 3000 + 4760 from rfl, factsOK_add, facts_5,
    Bool.true_and, show (15000 : ℕ) + 3000 = 18000 from rfl]
  rw [show (4760 : ℕ) = 3000 + 1760 from rfl, factsOK_add, facts_6,
    Bool.true_and, show (18000 : ℕ) + 3000 = 21000 from rfl]
  exact facts_7

theorem cover_0 : coverOK 7585 6 22760 fx fc fy (invLetter 3) ffi live 0 20000 = true := by
  decide +kernel

theorem cover_1 : coverOK 7585 6 22760 fx fc fy (invLetter 3) ffi live 20000 20000 = true := by
  decide +kernel

theorem cover_2 : coverOK 7585 6 22760 fx fc fy (invLetter 3) ffi live 40000 5510 = true := by
  decide +kernel

theorem cover_all : coverOK 7585 6 22760 fx fc fy (invLetter 3) ffi live 0 45510 = true := by
  rw [show (45510 : ℕ) = 20000 + 25510 from rfl, coverOK_add, cover_0,
    Bool.true_and, show (0 : ℕ) + 20000 = 20000 from rfl]
  rw [show (25510 : ℕ) = 20000 + 5510 from rfl, coverOK_add, cover_1,
    Bool.true_and, show (20000 : ℕ) + 20000 = 40000 from rfl]
  exact cover_2

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.SigmaFar.Data7560
