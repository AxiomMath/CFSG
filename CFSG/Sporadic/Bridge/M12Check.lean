module

public import CFSG.Sporadic.Bridge.M12Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Sporadic.Bridge.M12Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 0 4000 = true := by
  decide +kernel

theorem facts_1 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 4000 4000 = true := by
  decide +kernel

theorem facts_2 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 8000 4000 = true := by
  decide +kernel

theorem facts_3 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 12000 4000 = true := by
  decide +kernel

theorem facts_4 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 16000 4000 = true := by
  decide +kernel

theorem facts_5 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 20000 4000 = true := by
  decide +kernel

theorem facts_6 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 24000 4000 = true := by
  decide +kernel

theorem facts_7 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 28000 4000 = true := by
  decide +kernel

theorem facts_8 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 32000 4000 = true := by
  decide +kernel

theorem facts_9 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 36000 4000 = true := by
  decide +kernel

theorem facts_10 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 40000 4000 = true := by
  decide +kernel

theorem facts_11 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 44000 4000 = true := by
  decide +kernel

theorem facts_12 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 48000 4000 = true := by
  decide +kernel

theorem facts_13 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 52000 4000 = true := by
  decide +kernel

theorem facts_14 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 56000 4000 = true := by
  decide +kernel

theorem facts_15 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 60000 4000 = true := by
  decide +kernel

theorem facts_16 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 64000 4000 = true := by
  decide +kernel

theorem facts_17 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 68000 4000 = true := by
  decide +kernel

theorem facts_18 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 72000 4000 = true := by
  decide +kernel

theorem facts_19 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 76000 4000 = true := by
  decide +kernel

theorem facts_20 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 80000 4000 = true := by
  decide +kernel

theorem facts_21 : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 84000 1775 = true := by
  decide +kernel

theorem facts_all : factsOK 41575 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[3, 0]] 0 85775 = true := by
  rw [show (85775 : ℕ) = 4000 + 81775 from rfl, factsOK_add, facts_0, Bool.true_and, show (0 : ℕ) + 4000 = 4000 from rfl]
  rw [show (81775 : ℕ) = 4000 + 77775 from rfl, factsOK_add, facts_1, Bool.true_and, show (4000 : ℕ) + 4000 = 8000 from rfl]
  rw [show (77775 : ℕ) = 4000 + 73775 from rfl, factsOK_add, facts_2, Bool.true_and, show (8000 : ℕ) + 4000 = 12000 from rfl]
  rw [show (73775 : ℕ) = 4000 + 69775 from rfl, factsOK_add, facts_3, Bool.true_and, show (12000 : ℕ) + 4000 = 16000 from rfl]
  rw [show (69775 : ℕ) = 4000 + 65775 from rfl, factsOK_add, facts_4, Bool.true_and, show (16000 : ℕ) + 4000 = 20000 from rfl]
  rw [show (65775 : ℕ) = 4000 + 61775 from rfl, factsOK_add, facts_5, Bool.true_and, show (20000 : ℕ) + 4000 = 24000 from rfl]
  rw [show (61775 : ℕ) = 4000 + 57775 from rfl, factsOK_add, facts_6, Bool.true_and, show (24000 : ℕ) + 4000 = 28000 from rfl]
  rw [show (57775 : ℕ) = 4000 + 53775 from rfl, factsOK_add, facts_7, Bool.true_and, show (28000 : ℕ) + 4000 = 32000 from rfl]
  rw [show (53775 : ℕ) = 4000 + 49775 from rfl, factsOK_add, facts_8, Bool.true_and, show (32000 : ℕ) + 4000 = 36000 from rfl]
  rw [show (49775 : ℕ) = 4000 + 45775 from rfl, factsOK_add, facts_9, Bool.true_and, show (36000 : ℕ) + 4000 = 40000 from rfl]
  rw [show (45775 : ℕ) = 4000 + 41775 from rfl, factsOK_add, facts_10, Bool.true_and, show (40000 : ℕ) + 4000 = 44000 from rfl]
  rw [show (41775 : ℕ) = 4000 + 37775 from rfl, factsOK_add, facts_11, Bool.true_and, show (44000 : ℕ) + 4000 = 48000 from rfl]
  rw [show (37775 : ℕ) = 4000 + 33775 from rfl, factsOK_add, facts_12, Bool.true_and, show (48000 : ℕ) + 4000 = 52000 from rfl]
  rw [show (33775 : ℕ) = 4000 + 29775 from rfl, factsOK_add, facts_13, Bool.true_and, show (52000 : ℕ) + 4000 = 56000 from rfl]
  rw [show (29775 : ℕ) = 4000 + 25775 from rfl, factsOK_add, facts_14, Bool.true_and, show (56000 : ℕ) + 4000 = 60000 from rfl]
  rw [show (25775 : ℕ) = 4000 + 21775 from rfl, factsOK_add, facts_15, Bool.true_and, show (60000 : ℕ) + 4000 = 64000 from rfl]
  rw [show (21775 : ℕ) = 4000 + 17775 from rfl, factsOK_add, facts_16, Bool.true_and, show (64000 : ℕ) + 4000 = 68000 from rfl]
  rw [show (17775 : ℕ) = 4000 + 13775 from rfl, factsOK_add, facts_17, Bool.true_and, show (68000 : ℕ) + 4000 = 72000 from rfl]
  rw [show (13775 : ℕ) = 4000 + 9775 from rfl, factsOK_add, facts_18, Bool.true_and, show (72000 : ℕ) + 4000 = 76000 from rfl]
  rw [show (9775 : ℕ) = 4000 + 5775 from rfl, factsOK_add, facts_19, Bool.true_and, show (76000 : ℕ) + 4000 = 80000 from rfl]
  rw [show (5775 : ℕ) = 4000 + 1775 from rfl, factsOK_add, facts_20, Bool.true_and, show (80000 : ℕ) + 4000 = 84000 from rfl]
  exact facts_21

theorem cover_0 : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 0 20000 = true := by
  decide +kernel

theorem cover_1 : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 20000 20000 = true := by
  decide +kernel

theorem cover_2 : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 40000 20000 = true := by
  decide +kernel

theorem cover_3 : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 60000 20000 = true := by
  decide +kernel

theorem cover_4 : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 80000 20000 = true := by
  decide +kernel

theorem cover_5 : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 100000 20000 = true := by
  decide +kernel

theorem cover_6 : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 120000 20000 = true := by
  decide +kernel

theorem cover_7 : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 140000 20000 = true := by
  decide +kernel

theorem cover_8 : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 160000 6300 = true := by
  decide +kernel

theorem cover_all : coverOK 41575 4 85775 fx fc fy (invLetter 2) ffi live 0 166300 = true := by
  rw [show (166300 : ℕ) = 20000 + 146300 from rfl, coverOK_add, cover_0, Bool.true_and, show (0 : ℕ) + 20000 = 20000 from rfl]
  rw [show (146300 : ℕ) = 20000 + 126300 from rfl, coverOK_add, cover_1, Bool.true_and, show (20000 : ℕ) + 20000 = 40000 from rfl]
  rw [show (126300 : ℕ) = 20000 + 106300 from rfl, coverOK_add, cover_2, Bool.true_and, show (40000 : ℕ) + 20000 = 60000 from rfl]
  rw [show (106300 : ℕ) = 20000 + 86300 from rfl, coverOK_add, cover_3, Bool.true_and, show (60000 : ℕ) + 20000 = 80000 from rfl]
  rw [show (86300 : ℕ) = 20000 + 66300 from rfl, coverOK_add, cover_4, Bool.true_and, show (80000 : ℕ) + 20000 = 100000 from rfl]
  rw [show (66300 : ℕ) = 20000 + 46300 from rfl, coverOK_add, cover_5, Bool.true_and, show (100000 : ℕ) + 20000 = 120000 from rfl]
  rw [show (46300 : ℕ) = 20000 + 26300 from rfl, coverOK_add, cover_6, Bool.true_and, show (120000 : ℕ) + 20000 = 140000 from rfl]
  rw [show (26300 : ℕ) = 20000 + 6300 from rfl, coverOK_add, cover_7, Bool.true_and, show (140000 : ℕ) + 20000 = 160000 from rfl]
  exact cover_8

theorem liveCount_eq : liveCount live 41575 = 31680 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Sporadic.Bridge.M12Data
