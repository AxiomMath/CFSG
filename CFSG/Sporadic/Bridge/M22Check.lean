module

public import CFSG.Sporadic.Bridge.M22Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Sporadic.Bridge.M22Data.PowA

open CFSG.Certificates.CosetEnumeration

theorem facts_0 : factsOK 5317 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 0 2000 = true := by
  decide +kernel

theorem facts_1 : factsOK 5317 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 2000 2000 = true := by
  decide +kernel

theorem facts_2 : factsOK 5317 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 4000 2000 = true := by
  decide +kernel

theorem facts_3 : factsOK 5317 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 6000 2000 = true := by
  decide +kernel

theorem facts_4 : factsOK 5317 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 8000 642 = true := by
  decide +kernel

theorem facts_all : factsOK 5317 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 0 8642 = true := by
  rw [show (8642 : ℕ) = 2000 + 6642 from rfl, factsOK_add, facts_0, Bool.true_and, show (0 : ℕ) + 2000 = 2000 from rfl]
  rw [show (6642 : ℕ) = 2000 + 4642 from rfl, factsOK_add, facts_1, Bool.true_and, show (2000 : ℕ) + 2000 = 4000 from rfl]
  rw [show (4642 : ℕ) = 2000 + 2642 from rfl, factsOK_add, facts_2, Bool.true_and, show (4000 : ℕ) + 2000 = 6000 from rfl]
  rw [show (2642 : ℕ) = 2000 + 642 from rfl, factsOK_add, facts_3, Bool.true_and, show (6000 : ℕ) + 2000 = 8000 from rfl]
  exact facts_4

theorem close : walkOK fx fc fy (invLetter 2) refs 8642 0 24578 0 1 0 [0, 0, 0, 0, 0] = true := by
  decide +kernel

end CFSG.Sporadic.Bridge.M22Data.PowA

namespace CFSG.Sporadic.Bridge.M22Data.PowAbb

open CFSG.Certificates.CosetEnumeration

theorem facts_0 : factsOK 2533 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 0 2000 = true := by
  decide +kernel

theorem facts_1 : factsOK 2533 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 2000 1798 = true := by
  decide +kernel

theorem facts_all : factsOK 2533 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 0 3798 = true := by
  rw [show (3798 : ℕ) = 2000 + 1798 from rfl, factsOK_add, facts_0, Bool.true_and, show (0 : ℕ) + 2000 = 2000 from rfl]
  exact facts_1

theorem close : walkOK fx fc fy (invLetter 2) refs 3798 0 9723 0 1 0 [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2] = true := by
  decide +kernel

end CFSG.Sporadic.Bridge.M22Data.PowAbb

namespace CFSG.Sporadic.Bridge.M22Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 0 2000 = true := by
  decide +kernel

theorem facts_1 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 2000 2000 = true := by
  decide +kernel

theorem facts_2 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 4000 2000 = true := by
  decide +kernel

theorem facts_3 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 6000 2000 = true := by
  decide +kernel

theorem facts_4 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 8000 2000 = true := by
  decide +kernel

theorem facts_5 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 10000 2000 = true := by
  decide +kernel

theorem facts_6 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 12000 2000 = true := by
  decide +kernel

theorem facts_7 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 14000 2000 = true := by
  decide +kernel

theorem facts_8 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 16000 2000 = true := by
  decide +kernel

theorem facts_9 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 18000 2000 = true := by
  decide +kernel

theorem facts_10 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 20000 2000 = true := by
  decide +kernel

theorem facts_11 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 22000 2000 = true := by
  decide +kernel

theorem facts_12 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 24000 2000 = true := by
  decide +kernel

theorem facts_13 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 26000 2000 = true := by
  decide +kernel

theorem facts_14 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 28000 2000 = true := by
  decide +kernel

theorem facts_15 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 30000 2000 = true := by
  decide +kernel

theorem facts_16 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 32000 2000 = true := by
  decide +kernel

theorem facts_17 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 34000 2000 = true := by
  decide +kernel

theorem facts_18 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 36000 2000 = true := by
  decide +kernel

theorem facts_19 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 38000 2000 = true := by
  decide +kernel

theorem facts_20 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 40000 2000 = true := by
  decide +kernel

theorem facts_21 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 42000 2000 = true := by
  decide +kernel

theorem facts_22 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 44000 2000 = true := by
  decide +kernel

theorem facts_23 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 46000 2000 = true := by
  decide +kernel

theorem facts_24 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 48000 2000 = true := by
  decide +kernel

theorem facts_25 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 50000 2000 = true := by
  decide +kernel

theorem facts_26 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 52000 2000 = true := by
  decide +kernel

theorem facts_27 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 54000 2000 = true := by
  decide +kernel

theorem facts_28 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 56000 2000 = true := by
  decide +kernel

theorem facts_29 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 58000 2000 = true := by
  decide +kernel

theorem facts_30 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 60000 2000 = true := by
  decide +kernel

theorem facts_31 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 62000 2000 = true := by
  decide +kernel

theorem facts_32 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 64000 2000 = true := by
  decide +kernel

theorem facts_33 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 66000 2000 = true := by
  decide +kernel

theorem facts_34 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 68000 2000 = true := by
  decide +kernel

theorem facts_35 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 70000 2000 = true := by
  decide +kernel

theorem facts_36 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 72000 2000 = true := by
  decide +kernel

theorem facts_37 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 74000 2000 = true := by
  decide +kernel

theorem facts_38 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 76000 2000 = true := by
  decide +kernel

theorem facts_39 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 78000 2000 = true := by
  decide +kernel

theorem facts_40 : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 80000 1016 = true := by
  decide +kernel

theorem facts_all : factsOK 40460 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [[2]] 0 81016 = true := by
  rw [show (81016 : ℕ) = 2000 + 79016 from rfl, factsOK_add, facts_0, Bool.true_and, show (0 : ℕ) + 2000 = 2000 from rfl]
  rw [show (79016 : ℕ) = 2000 + 77016 from rfl, factsOK_add, facts_1, Bool.true_and, show (2000 : ℕ) + 2000 = 4000 from rfl]
  rw [show (77016 : ℕ) = 2000 + 75016 from rfl, factsOK_add, facts_2, Bool.true_and, show (4000 : ℕ) + 2000 = 6000 from rfl]
  rw [show (75016 : ℕ) = 2000 + 73016 from rfl, factsOK_add, facts_3, Bool.true_and, show (6000 : ℕ) + 2000 = 8000 from rfl]
  rw [show (73016 : ℕ) = 2000 + 71016 from rfl, factsOK_add, facts_4, Bool.true_and, show (8000 : ℕ) + 2000 = 10000 from rfl]
  rw [show (71016 : ℕ) = 2000 + 69016 from rfl, factsOK_add, facts_5, Bool.true_and, show (10000 : ℕ) + 2000 = 12000 from rfl]
  rw [show (69016 : ℕ) = 2000 + 67016 from rfl, factsOK_add, facts_6, Bool.true_and, show (12000 : ℕ) + 2000 = 14000 from rfl]
  rw [show (67016 : ℕ) = 2000 + 65016 from rfl, factsOK_add, facts_7, Bool.true_and, show (14000 : ℕ) + 2000 = 16000 from rfl]
  rw [show (65016 : ℕ) = 2000 + 63016 from rfl, factsOK_add, facts_8, Bool.true_and, show (16000 : ℕ) + 2000 = 18000 from rfl]
  rw [show (63016 : ℕ) = 2000 + 61016 from rfl, factsOK_add, facts_9, Bool.true_and, show (18000 : ℕ) + 2000 = 20000 from rfl]
  rw [show (61016 : ℕ) = 2000 + 59016 from rfl, factsOK_add, facts_10, Bool.true_and, show (20000 : ℕ) + 2000 = 22000 from rfl]
  rw [show (59016 : ℕ) = 2000 + 57016 from rfl, factsOK_add, facts_11, Bool.true_and, show (22000 : ℕ) + 2000 = 24000 from rfl]
  rw [show (57016 : ℕ) = 2000 + 55016 from rfl, factsOK_add, facts_12, Bool.true_and, show (24000 : ℕ) + 2000 = 26000 from rfl]
  rw [show (55016 : ℕ) = 2000 + 53016 from rfl, factsOK_add, facts_13, Bool.true_and, show (26000 : ℕ) + 2000 = 28000 from rfl]
  rw [show (53016 : ℕ) = 2000 + 51016 from rfl, factsOK_add, facts_14, Bool.true_and, show (28000 : ℕ) + 2000 = 30000 from rfl]
  rw [show (51016 : ℕ) = 2000 + 49016 from rfl, factsOK_add, facts_15, Bool.true_and, show (30000 : ℕ) + 2000 = 32000 from rfl]
  rw [show (49016 : ℕ) = 2000 + 47016 from rfl, factsOK_add, facts_16, Bool.true_and, show (32000 : ℕ) + 2000 = 34000 from rfl]
  rw [show (47016 : ℕ) = 2000 + 45016 from rfl, factsOK_add, facts_17, Bool.true_and, show (34000 : ℕ) + 2000 = 36000 from rfl]
  rw [show (45016 : ℕ) = 2000 + 43016 from rfl, factsOK_add, facts_18, Bool.true_and, show (36000 : ℕ) + 2000 = 38000 from rfl]
  rw [show (43016 : ℕ) = 2000 + 41016 from rfl, factsOK_add, facts_19, Bool.true_and, show (38000 : ℕ) + 2000 = 40000 from rfl]
  rw [show (41016 : ℕ) = 2000 + 39016 from rfl, factsOK_add, facts_20, Bool.true_and, show (40000 : ℕ) + 2000 = 42000 from rfl]
  rw [show (39016 : ℕ) = 2000 + 37016 from rfl, factsOK_add, facts_21, Bool.true_and, show (42000 : ℕ) + 2000 = 44000 from rfl]
  rw [show (37016 : ℕ) = 2000 + 35016 from rfl, factsOK_add, facts_22, Bool.true_and, show (44000 : ℕ) + 2000 = 46000 from rfl]
  rw [show (35016 : ℕ) = 2000 + 33016 from rfl, factsOK_add, facts_23, Bool.true_and, show (46000 : ℕ) + 2000 = 48000 from rfl]
  rw [show (33016 : ℕ) = 2000 + 31016 from rfl, factsOK_add, facts_24, Bool.true_and, show (48000 : ℕ) + 2000 = 50000 from rfl]
  rw [show (31016 : ℕ) = 2000 + 29016 from rfl, factsOK_add, facts_25, Bool.true_and, show (50000 : ℕ) + 2000 = 52000 from rfl]
  rw [show (29016 : ℕ) = 2000 + 27016 from rfl, factsOK_add, facts_26, Bool.true_and, show (52000 : ℕ) + 2000 = 54000 from rfl]
  rw [show (27016 : ℕ) = 2000 + 25016 from rfl, factsOK_add, facts_27, Bool.true_and, show (54000 : ℕ) + 2000 = 56000 from rfl]
  rw [show (25016 : ℕ) = 2000 + 23016 from rfl, factsOK_add, facts_28, Bool.true_and, show (56000 : ℕ) + 2000 = 58000 from rfl]
  rw [show (23016 : ℕ) = 2000 + 21016 from rfl, factsOK_add, facts_29, Bool.true_and, show (58000 : ℕ) + 2000 = 60000 from rfl]
  rw [show (21016 : ℕ) = 2000 + 19016 from rfl, factsOK_add, facts_30, Bool.true_and, show (60000 : ℕ) + 2000 = 62000 from rfl]
  rw [show (19016 : ℕ) = 2000 + 17016 from rfl, factsOK_add, facts_31, Bool.true_and, show (62000 : ℕ) + 2000 = 64000 from rfl]
  rw [show (17016 : ℕ) = 2000 + 15016 from rfl, factsOK_add, facts_32, Bool.true_and, show (64000 : ℕ) + 2000 = 66000 from rfl]
  rw [show (15016 : ℕ) = 2000 + 13016 from rfl, factsOK_add, facts_33, Bool.true_and, show (66000 : ℕ) + 2000 = 68000 from rfl]
  rw [show (13016 : ℕ) = 2000 + 11016 from rfl, factsOK_add, facts_34, Bool.true_and, show (68000 : ℕ) + 2000 = 70000 from rfl]
  rw [show (11016 : ℕ) = 2000 + 9016 from rfl, factsOK_add, facts_35, Bool.true_and, show (70000 : ℕ) + 2000 = 72000 from rfl]
  rw [show (9016 : ℕ) = 2000 + 7016 from rfl, factsOK_add, facts_36, Bool.true_and, show (72000 : ℕ) + 2000 = 74000 from rfl]
  rw [show (7016 : ℕ) = 2000 + 5016 from rfl, factsOK_add, facts_37, Bool.true_and, show (74000 : ℕ) + 2000 = 76000 from rfl]
  rw [show (5016 : ℕ) = 2000 + 3016 from rfl, factsOK_add, facts_38, Bool.true_and, show (76000 : ℕ) + 2000 = 78000 from rfl]
  rw [show (3016 : ℕ) = 2000 + 1016 from rfl, factsOK_add, facts_39, Bool.true_and, show (78000 : ℕ) + 2000 = 80000 from rfl]
  exact facts_40

theorem cover_0 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 0 10000 = true := by
  decide +kernel

theorem cover_1 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 10000 10000 = true := by
  decide +kernel

theorem cover_2 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 20000 10000 = true := by
  decide +kernel

theorem cover_3 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 30000 10000 = true := by
  decide +kernel

theorem cover_4 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 40000 10000 = true := by
  decide +kernel

theorem cover_5 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 50000 10000 = true := by
  decide +kernel

theorem cover_6 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 60000 10000 = true := by
  decide +kernel

theorem cover_7 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 70000 10000 = true := by
  decide +kernel

theorem cover_8 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 80000 10000 = true := by
  decide +kernel

theorem cover_9 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 90000 10000 = true := by
  decide +kernel

theorem cover_10 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 100000 10000 = true := by
  decide +kernel

theorem cover_11 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 110000 10000 = true := by
  decide +kernel

theorem cover_12 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 120000 10000 = true := by
  decide +kernel

theorem cover_13 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 130000 10000 = true := by
  decide +kernel

theorem cover_14 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 140000 10000 = true := by
  decide +kernel

theorem cover_15 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 150000 10000 = true := by
  decide +kernel

theorem cover_16 : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 160000 1840 = true := by
  decide +kernel

theorem cover_all : coverOK 40460 4 81016 fx fc fy (invLetter 2) ffi live 0 161840 = true := by
  rw [show (161840 : ℕ) = 10000 + 151840 from rfl, coverOK_add, cover_0, Bool.true_and, show (0 : ℕ) + 10000 = 10000 from rfl]
  rw [show (151840 : ℕ) = 10000 + 141840 from rfl, coverOK_add, cover_1, Bool.true_and, show (10000 : ℕ) + 10000 = 20000 from rfl]
  rw [show (141840 : ℕ) = 10000 + 131840 from rfl, coverOK_add, cover_2, Bool.true_and, show (20000 : ℕ) + 10000 = 30000 from rfl]
  rw [show (131840 : ℕ) = 10000 + 121840 from rfl, coverOK_add, cover_3, Bool.true_and, show (30000 : ℕ) + 10000 = 40000 from rfl]
  rw [show (121840 : ℕ) = 10000 + 111840 from rfl, coverOK_add, cover_4, Bool.true_and, show (40000 : ℕ) + 10000 = 50000 from rfl]
  rw [show (111840 : ℕ) = 10000 + 101840 from rfl, coverOK_add, cover_5, Bool.true_and, show (50000 : ℕ) + 10000 = 60000 from rfl]
  rw [show (101840 : ℕ) = 10000 + 91840 from rfl, coverOK_add, cover_6, Bool.true_and, show (60000 : ℕ) + 10000 = 70000 from rfl]
  rw [show (91840 : ℕ) = 10000 + 81840 from rfl, coverOK_add, cover_7, Bool.true_and, show (70000 : ℕ) + 10000 = 80000 from rfl]
  rw [show (81840 : ℕ) = 10000 + 71840 from rfl, coverOK_add, cover_8, Bool.true_and, show (80000 : ℕ) + 10000 = 90000 from rfl]
  rw [show (71840 : ℕ) = 10000 + 61840 from rfl, coverOK_add, cover_9, Bool.true_and, show (90000 : ℕ) + 10000 = 100000 from rfl]
  rw [show (61840 : ℕ) = 10000 + 51840 from rfl, coverOK_add, cover_10, Bool.true_and, show (100000 : ℕ) + 10000 = 110000 from rfl]
  rw [show (51840 : ℕ) = 10000 + 41840 from rfl, coverOK_add, cover_11, Bool.true_and, show (110000 : ℕ) + 10000 = 120000 from rfl]
  rw [show (41840 : ℕ) = 10000 + 31840 from rfl, coverOK_add, cover_12, Bool.true_and, show (120000 : ℕ) + 10000 = 130000 from rfl]
  rw [show (31840 : ℕ) = 10000 + 21840 from rfl, coverOK_add, cover_13, Bool.true_and, show (130000 : ℕ) + 10000 = 140000 from rfl]
  rw [show (21840 : ℕ) = 10000 + 11840 from rfl, coverOK_add, cover_14, Bool.true_and, show (140000 : ℕ) + 10000 = 150000 from rfl]
  rw [show (11840 : ℕ) = 10000 + 1840 from rfl, coverOK_add, cover_15, Bool.true_and, show (150000 : ℕ) + 10000 = 160000 from rfl]
  exact cover_16

theorem liveCount_eq : liveCount live 40460 = 40320 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Sporadic.Bridge.M22Data
