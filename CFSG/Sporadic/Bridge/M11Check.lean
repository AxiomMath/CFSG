module

public import Certificates.Certificate110


public section

namespace CFSG.Sporadic.Bridge.M11Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 0 4000 = true := by
  exact Certificates.certificate110.1

theorem facts_1 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 4000 4000 = true := by
  exact Certificates.certificate110.2.1

theorem facts_2 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 8000 4000 = true := by
  exact Certificates.certificate110.2.2.1

theorem facts_3 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 12000 4000 = true := by
  exact Certificates.certificate110.2.2.2.1

theorem facts_4 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 16000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.1

theorem facts_5 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 20000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.1

theorem facts_6 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 24000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.1

theorem facts_7 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 28000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.1

theorem facts_8 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 32000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.1

theorem facts_9 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 36000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.1

theorem facts_10 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 40000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.1

theorem facts_11 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 44000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.1

theorem facts_12 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 48000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem facts_13 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 52000 4000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem facts_14 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 56000 14 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem facts_all : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 0 56014 = true := by
  rw [show (56014 : ℕ) = 4000 + 52014 from rfl, factsOK_add, facts_0, Bool.true_and, show (0 : ℕ) + 4000 = 4000 from rfl]
  rw [show (52014 : ℕ) = 4000 + 48014 from rfl, factsOK_add, facts_1, Bool.true_and, show (4000 : ℕ) + 4000 = 8000 from rfl]
  rw [show (48014 : ℕ) = 4000 + 44014 from rfl, factsOK_add, facts_2, Bool.true_and, show (8000 : ℕ) + 4000 = 12000 from rfl]
  rw [show (44014 : ℕ) = 4000 + 40014 from rfl, factsOK_add, facts_3, Bool.true_and, show (12000 : ℕ) + 4000 = 16000 from rfl]
  rw [show (40014 : ℕ) = 4000 + 36014 from rfl, factsOK_add, facts_4, Bool.true_and, show (16000 : ℕ) + 4000 = 20000 from rfl]
  rw [show (36014 : ℕ) = 4000 + 32014 from rfl, factsOK_add, facts_5, Bool.true_and, show (20000 : ℕ) + 4000 = 24000 from rfl]
  rw [show (32014 : ℕ) = 4000 + 28014 from rfl, factsOK_add, facts_6, Bool.true_and, show (24000 : ℕ) + 4000 = 28000 from rfl]
  rw [show (28014 : ℕ) = 4000 + 24014 from rfl, factsOK_add, facts_7, Bool.true_and, show (28000 : ℕ) + 4000 = 32000 from rfl]
  rw [show (24014 : ℕ) = 4000 + 20014 from rfl, factsOK_add, facts_8, Bool.true_and, show (32000 : ℕ) + 4000 = 36000 from rfl]
  rw [show (20014 : ℕ) = 4000 + 16014 from rfl, factsOK_add, facts_9, Bool.true_and, show (36000 : ℕ) + 4000 = 40000 from rfl]
  rw [show (16014 : ℕ) = 4000 + 12014 from rfl, factsOK_add, facts_10, Bool.true_and, show (40000 : ℕ) + 4000 = 44000 from rfl]
  rw [show (12014 : ℕ) = 4000 + 8014 from rfl, factsOK_add, facts_11, Bool.true_and, show (44000 : ℕ) + 4000 = 48000 from rfl]
  rw [show (8014 : ℕ) = 4000 + 4014 from rfl, factsOK_add, facts_12, Bool.true_and, show (48000 : ℕ) + 4000 = 52000 from rfl]
  rw [show (4014 : ℕ) = 4000 + 14 from rfl, factsOK_add, facts_13, Bool.true_and, show (52000 : ℕ) + 4000 = 56000 from rfl]
  exact facts_14

theorem cover_0 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 0 20000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cover_1 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 20000 20000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cover_2 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 40000 20000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cover_3 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 60000 20000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cover_4 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 80000 20000 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cover_5 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 100000 2592 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cover_all : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 0 102592 = true := by
  rw [show (102592 : ℕ) = 20000 + 82592 from rfl, coverOK_add, cover_0, Bool.true_and, show (0 : ℕ) + 20000 = 20000 from rfl]
  rw [show (82592 : ℕ) = 20000 + 62592 from rfl, coverOK_add, cover_1, Bool.true_and, show (20000 : ℕ) + 20000 = 40000 from rfl]
  rw [show (62592 : ℕ) = 20000 + 42592 from rfl, coverOK_add, cover_2, Bool.true_and, show (40000 : ℕ) + 20000 = 60000 from rfl]
  rw [show (42592 : ℕ) = 20000 + 22592 from rfl, coverOK_add, cover_3, Bool.true_and, show (60000 : ℕ) + 20000 = 80000 from rfl]
  rw [show (22592 : ℕ) = 20000 + 2592 from rfl, coverOK_add, cover_4, Bool.true_and, show (80000 : ℕ) + 20000 = 100000 from rfl]
  exact cover_5

theorem liveCount_eq : liveCount live 25648 = 7920 := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem live_zero : live 0 = true := by
  exact Certificates.certificate110.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.Bridge.M11Data
