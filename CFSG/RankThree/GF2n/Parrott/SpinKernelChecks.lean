module

public import Certificates.Data.ParrottSpinA

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Parrott

private def spinVec (n : ℕ) : V := fun i => ((n >>> (i : ℕ)) % 2 : ℕ)

private def spinQTable : List ℕ := (List.range 256).map fun n => (q (spinVec n)).val

private theorem q_val_eq_spinQTable : ∀ v : V, (q v).val = spinQTable.getD (bitmask v) 0 := by
  decide +kernel

private theorem q_mulVec_of_bitRow (M : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (h : ∀ v : V, spinQTable.getD (bitRow M (bitmask v)) 0 = spinQTable.getD (bitmask v) 0)
    (v : V) : q (M *ᵥ v) = q v := by
  apply ZMod.val_injective
  rw [q_val_eq_spinQTable, q_val_eq_spinQTable, ← bitRow_bitmask]
  exact h v

private theorem spinQTable_invariant :
    ∀ v : V, (spinQTable.getD (bitRow Mx (bitmask v)) 0 = spinQTable.getD (bitmask v) 0) ∧
      (spinQTable.getD (bitRow My (bitmask v)) 0 = spinQTable.getD (bitmask v) 0) ∧
      (spinQTable.getD (bitRow Mf (bitmask v)) 0 = spinQTable.getD (bitmask v) 0) := by
  decide +kernel

theorem q_mulVec_Mx (v : V) : q (Mx *ᵥ v) = q v :=
  q_mulVec_of_bitRow Mx (fun w => (spinQTable_invariant w).1) v

theorem q_mulVec_My (v : V) : q (My *ᵥ v) = q v :=
  q_mulVec_of_bitRow My (fun w => (spinQTable_invariant w).2.1) v

theorem q_mulVec_Mf (v : V) : q (Mf *ᵥ v) = q v :=
  q_mulVec_of_bitRow Mf (fun w => (spinQTable_invariant w).2.2) v

@[expose] def spinSingBase : V := basis 1

@[expose] def spinNonBase : V := basis 0

private def spinDecode : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, c => if c ≤ 1 then [] else (c % 2 == 1) :: spinDecode n (c / 2)

private def spinSingTable : List (ℕ × ℕ) :=
  [ (2, 1), (4, 475), (7, 2743), (12, 4021), (13, 957), (17, 27), (19, 1725), (21, 54), (22, 7515),
    (24, 2), (25, 5486), (26, 3831), (27, 10), (30, 8043), (31, 5), (38, 107), (39, 13),
    (40, 1903), (42, 887), (45, 1879), (46, 1774), (54, 3806), (55, 3758), (56, 214), (58, 859),
    (61, 26), (62, 1718), (64, 187), (66, 6903), (68, 43), (71, 3438), (76, 110), (77, 1494),
    (81, 939), (83, 747), (85, 1878), (86, 55), (88, 3549), (89, 1719), (90, 3567), (91, 31),
    (94, 30063), (95, 62), (96, 1005), (97, 15), (98, 431), (99, 42), (100, 2010), (101, 221),
    (105, 118), (107, 119), (108, 23), (111, 855), (112, 478), (113, 3435), (114, 46), (115, 59),
    (116, 239), (117, 1783), (121, 21), (123, 375), (124, 862), (127, 891), (128, 1495),
    (129, 502), (132, 21943), (133, 251), (134, 1902), (135, 469), (137, 342), (138, 10971),
    (140, 2742), (142, 47), (144, 2011), (145, 14), (148, 213), (149, 7), (150, 1371), (151, 171),
    (153, 445), (154, 3805), (156, 951), (158, 125), (160, 93), (163, 53), (164, 186), (166, 1717),
    (170, 427), (171, 2991), (172, 15031), (173, 3), (174, 854), (175, 3439), (177, 3757),
    (178, 7663), (181, 5485), (183, 6), (184, 1007), (185, 106), (192, 3005), (193, 117),
    (196, 1775), (197, 234), (198, 746), (199, 443), (201, 222), (202, 109), (204, 343),
    (206, 687), (208, 6011), (209, 3830), (212, 10973), (213, 1915), (214, 686), (215, 111),
    (217, 237), (218, 215), (220, 373), (222, 439), (225, 1493), (226, 685), (229, 11), (231, 58),
    (232, 170), (233, 751), (240, 858), (243, 1502), (244, 429), (246, 85), (250, 1758),
    (251, 3451), (252, 503), (253, 29), (254, 879), (255, 219)]

private def spinNonTable : List (ℕ × ℕ) :=
  [ (1, 1), (3, 1498), (5, 2), (6, 22), (8, 183), (9, 175), (10, 3797), (11, 213), (14, 2799),
    (15, 379), (16, 493), (18, 117), (20, 31), (23, 350), (28, 11), (29, 749), (32, 695),
    (33, 347), (34, 118), (35, 885), (36, 1390), (37, 107), (41, 123), (43, 189), (44, 42),
    (47, 7595), (48, 14), (49, 45), (50, 21), (51, 246), (52, 7), (53, 173), (57, 699), (59, 1709),
    (60, 59), (63, 1399), (65, 1374), (67, 374), (69, 687), (70, 237), (72, 1499), (73, 10),
    (74, 475), (75, 3931), (78, 981), (79, 6077), (80, 7085), (82, 1965), (84, 951), (87, 5),
    (92, 474), (93, 187), (102, 1518), (103, 110), (104, 58), (106, 221), (109, 343), (110, 442),
    (118, 29), (119, 686), (120, 759), (122, 1903), (125, 55), (126, 3543), (130, 367), (131, 23),
    (136, 61), (139, 3038), (141, 1771), (143, 1519), (146, 122), (147, 3542), (152, 734),
    (155, 245), (157, 46), (159, 490), (161, 3037), (162, 247), (165, 887), (167, 182), (168, 13),
    (169, 87), (176, 2749), (179, 174), (180, 1469), (182, 26), (186, 365), (187, 349), (188, 215),
    (189, 91), (190, 730), (191, 443), (194, 27), (195, 431), (200, 982), (203, 3), (205, 47),
    (207, 6), (210, 491), (211, 94), (216, 54), (219, 43), (221, 862), (223, 86), (224, 854),
    (227, 93), (228, 427), (230, 1898), (234, 15), (235, 1391), (236, 53), (237, 495), (238, 30),
    (239, 373), (241, 171), (242, 106), (245, 85), (247, 990), (248, 949), (249, 186)]

private theorem spinSingTable_reach : ∀ v : V, v ≠ 0 → q v = 0 →
    bitWord (toSpinWord (spinDecode 16 ((spinSingTable.lookup (bitmask v)).getD 1)))
      (bitmask spinSingBase) = bitmask v := by
  decide +kernel

private theorem spinNonTable_reach : ∀ v : V, q v = 1 →
    bitWord (toSpinWord (spinDecode 16 ((spinNonTable.lookup (bitmask v)).getD 1)))
      (bitmask spinNonBase) = bitmask v := by
  decide +kernel

theorem exists_word_sing (v : V) (hv : v ≠ 0) (hq : q v = 0) :
    ∃ w : List Bool, evalSpinWordV (toSpinWord w) spinSingBase = v :=
  ⟨_, bitmask_injective (by rw [← bitWord_bitmask]; exact spinSingTable_reach v hv hq)⟩

theorem exists_word_non (v : V) (hq : q v = 1) :
    ∃ w : List Bool, evalSpinWordV (toSpinWord w) spinNonBase = v :=
  ⟨_, bitmask_injective (by rw [← bitWord_bitmask]; exact spinNonTable_reach v hq)⟩

@[expose] def spinOrbitForm (a c : ZMod 2) (v : V) : ZMod 2 :=
  if v = 0 then 0 else if q v = 0 then a else c

theorem spinOrbitForm_zero_one (v : V) : spinOrbitForm 0 1 v = q v := by
  unfold spinOrbitForm
  split_ifs with h0 h1
  · subst h0
    simp [q]
  · exact h1.symm
  · revert h1
    generalize q v = x
    revert x
    decide

theorem spinOrbitForm_second_difference (c : ZMod 2) (Q : V → ZMod 2)
    (hQ : Q = spinOrbitForm 1 c) :
    Q (basis 7 + basis 6 + basis 5) + Q (basis 7 + basis 6) + Q (basis 7 + basis 5) +
      Q (basis 6 + basis 5) + Q (basis 7) + Q (basis 6) + Q (basis 5) ≠ 0 := by
  subst hQ
  revert c
  decide +kernel

end CFSG.RankThree.GF2n.Parrott
