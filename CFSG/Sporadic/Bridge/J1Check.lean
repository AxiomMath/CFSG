module

public import CFSG.Sporadic.Bridge.J1Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Sporadic.Bridge.J1Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 0 3000 = true := by
  decide +kernel

theorem facts_1 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 3000 3000 = true := by
  decide +kernel

theorem facts_2 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 6000 3000 = true := by
  decide +kernel

theorem facts_3 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 9000 3000 = true := by
  decide +kernel

theorem facts_4 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 12000 3000 = true := by
  decide +kernel

theorem facts_5 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 15000 3000 = true := by
  decide +kernel

theorem facts_6 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 18000 3000 = true := by
  decide +kernel

theorem facts_7 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 21000 3000 = true := by
  decide +kernel

theorem facts_8 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 24000 3000 = true := by
  decide +kernel

theorem facts_9 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 27000 3000 = true := by
  decide +kernel

theorem facts_10 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 30000 3000 = true := by
  decide +kernel

theorem facts_11 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 33000 3000 = true := by
  decide +kernel

theorem facts_12 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 36000 3000 = true := by
  decide +kernel

theorem facts_13 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 39000 3000 = true := by
  decide +kernel

theorem facts_14 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 42000 3000 = true := by
  decide +kernel

theorem facts_15 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 45000 3000 = true := by
  decide +kernel

theorem facts_16 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 48000 3000 = true := by
  decide +kernel

theorem facts_17 :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 51000 839 = true := by
  decide +kernel

theorem facts_all :
    factsOK 25653 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[0, 2]] 0 51839 = true := by
  rw [show (51839 : ℕ) = 3000 + 48839 from rfl, factsOK_add, facts_0, Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (48839 : ℕ) = 3000 + 45839 from rfl, factsOK_add, facts_1, Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  rw [show (45839 : ℕ) = 3000 + 42839 from rfl, factsOK_add, facts_2, Bool.true_and, show (6000 : ℕ) + 3000 = 9000 from rfl]
  rw [show (42839 : ℕ) = 3000 + 39839 from rfl, factsOK_add, facts_3, Bool.true_and, show (9000 : ℕ) + 3000 = 12000 from rfl]
  rw [show (39839 : ℕ) = 3000 + 36839 from rfl, factsOK_add, facts_4, Bool.true_and, show (12000 : ℕ) + 3000 = 15000 from rfl]
  rw [show (36839 : ℕ) = 3000 + 33839 from rfl, factsOK_add, facts_5, Bool.true_and, show (15000 : ℕ) + 3000 = 18000 from rfl]
  rw [show (33839 : ℕ) = 3000 + 30839 from rfl, factsOK_add, facts_6, Bool.true_and, show (18000 : ℕ) + 3000 = 21000 from rfl]
  rw [show (30839 : ℕ) = 3000 + 27839 from rfl, factsOK_add, facts_7, Bool.true_and, show (21000 : ℕ) + 3000 = 24000 from rfl]
  rw [show (27839 : ℕ) = 3000 + 24839 from rfl, factsOK_add, facts_8, Bool.true_and, show (24000 : ℕ) + 3000 = 27000 from rfl]
  rw [show (24839 : ℕ) = 3000 + 21839 from rfl, factsOK_add, facts_9, Bool.true_and, show (27000 : ℕ) + 3000 = 30000 from rfl]
  rw [show (21839 : ℕ) = 3000 + 18839 from rfl, factsOK_add, facts_10, Bool.true_and, show (30000 : ℕ) + 3000 = 33000 from rfl]
  rw [show (18839 : ℕ) = 3000 + 15839 from rfl, factsOK_add, facts_11, Bool.true_and, show (33000 : ℕ) + 3000 = 36000 from rfl]
  rw [show (15839 : ℕ) = 3000 + 12839 from rfl, factsOK_add, facts_12, Bool.true_and, show (36000 : ℕ) + 3000 = 39000 from rfl]
  rw [show (12839 : ℕ) = 3000 + 9839 from rfl, factsOK_add, facts_13, Bool.true_and, show (39000 : ℕ) + 3000 = 42000 from rfl]
  rw [show (9839 : ℕ) = 3000 + 6839 from rfl, factsOK_add, facts_14, Bool.true_and, show (42000 : ℕ) + 3000 = 45000 from rfl]
  rw [show (6839 : ℕ) = 3000 + 3839 from rfl, factsOK_add, facts_15, Bool.true_and, show (45000 : ℕ) + 3000 = 48000 from rfl]
  rw [show (3839 : ℕ) = 3000 + 839 from rfl, factsOK_add, facts_16, Bool.true_and, show (48000 : ℕ) + 3000 = 51000 from rfl]
  exact facts_17

theorem cover_0 : coverOK 25653 4 51839 fx fc fy (invLetter 2) ffi live 0 20000 = true := by
  decide +kernel

theorem cover_1 : coverOK 25653 4 51839 fx fc fy (invLetter 2) ffi live 20000 20000 = true := by
  decide +kernel

theorem cover_2 : coverOK 25653 4 51839 fx fc fy (invLetter 2) ffi live 40000 20000 = true := by
  decide +kernel

theorem cover_3 : coverOK 25653 4 51839 fx fc fy (invLetter 2) ffi live 60000 20000 = true := by
  decide +kernel

theorem cover_4 : coverOK 25653 4 51839 fx fc fy (invLetter 2) ffi live 80000 20000 = true := by
  decide +kernel

theorem cover_5 : coverOK 25653 4 51839 fx fc fy (invLetter 2) ffi live 100000 2612 = true := by
  decide +kernel

theorem cover_all : coverOK 25653 4 51839 fx fc fy (invLetter 2) ffi live 0 102612 = true := by
  rw [show (102612 : ℕ) = 20000 + 82612 from rfl, coverOK_add, cover_0, Bool.true_and, show (0 : ℕ) + 20000 = 20000 from rfl]
  rw [show (82612 : ℕ) = 20000 + 62612 from rfl, coverOK_add, cover_1, Bool.true_and, show (20000 : ℕ) + 20000 = 40000 from rfl]
  rw [show (62612 : ℕ) = 20000 + 42612 from rfl, coverOK_add, cover_2, Bool.true_and, show (40000 : ℕ) + 20000 = 60000 from rfl]
  rw [show (42612 : ℕ) = 20000 + 22612 from rfl, coverOK_add, cover_3, Bool.true_and, show (60000 : ℕ) + 20000 = 80000 from rfl]
  rw [show (22612 : ℕ) = 20000 + 2612 from rfl, coverOK_add, cover_4, Bool.true_and, show (80000 : ℕ) + 20000 = 100000 from rfl]
  exact cover_5

theorem liveCount_eq : liveCount live 25653 = 25080 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Sporadic.Bridge.J1Data
