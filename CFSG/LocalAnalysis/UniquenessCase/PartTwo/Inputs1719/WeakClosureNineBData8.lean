module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open CFSG.QuasithinUnique.A6Facts Subgroup

set_option maxRecDepth 100000

@[expose] def pb : Equiv.Perm (Fin 8) where
  toFun := ![7, 6, 3, 2, 5, 4, 1, 0]
  invFun := ![7, 6, 3, 2, 5, 4, 1, 0]
  left_inv := by decide
  right_inv := by decide

@[expose] def pu : Equiv.Perm (Fin 8) where
  toFun := ![2, 5, 4, 1, 7, 6, 3, 0]
  invFun := ![7, 3, 0, 6, 2, 1, 5, 4]
  left_inv := by decide
  right_inv := by decide

@[expose] def pv : Equiv.Perm (Fin 8) where
  toFun := ![1, 0, 3, 2, 6, 7, 4, 5]
  invFun := ![1, 0, 3, 2, 6, 7, 4, 5]
  left_inv := by decide
  right_inv := by decide

@[expose] def pw : Equiv.Perm (Fin 8) where
  toFun := ![1, 7, 4, 5, 3, 2, 0, 6]
  invFun := ![6, 0, 5, 4, 2, 3, 7, 1]
  left_inv := by decide
  right_inv := by decide

@[expose] def H0 : Subgroup (Equiv.Perm (Fin 8)) := closure {g | g ∈ [NFF7.g1, pb]}

@[expose] def D : Subgroup (Equiv.Perm (Fin 8)) := closure {g | g ∈ [pu, pv]}

@[expose] def D16 : Subgroup (Equiv.Perm (Fin 8)) := closure {g | g ∈ [pu, pv, NFF7.g2]}

@[expose] def hGenC : List (List ℕ) := [[1, 2, 3, 4, 5, 6, 0, 7], [7, 6, 3, 2, 5, 4, 1, 0]]

@[expose] def hTree : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0), (3, 1), (4, 0), (5, 0), (5, 1), (6, 0), (6, 1), (7, 0), (8, 0), (8, 1), (9, 0), (9, 1), (10, 0), (11, 0), (11, 1), (12, 0), (13, 0), (13, 1), (14, 0), (14, 1), (16, 0), (16, 1), (17, 0), (18, 0), (18, 1), (19, 1), (20, 0), (21, 0), (21, 1), (22, 0), (22, 1), (24, 0), (24, 1), (25, 0), (26, 0), (26, 1), (27, 0), (28, 0), (28, 1), (29, 0), (29, 1), (31, 0), (32, 0), (32, 1), (33, 0), (33, 1), (35, 0), (35, 1), (36, 0), (37, 0), (37, 1), (38, 0), (39, 0), (41, 0), (42, 0), (42, 1), (43, 0), (43, 1), (45, 0), (45, 1), (47, 0), (47, 1), (48, 0), (48, 1), (50, 0), (50, 1), (51, 0), (52, 0), (52, 1), (53, 0), (54, 0), (56, 0), (57, 0), (57, 1), (58, 0), (58, 1), (59, 0), (59, 1), (60, 0), (60, 1), (62, 0), (62, 1), (63, 0), (64, 0), (64, 1), (65, 0), (66, 0), (66, 1), (68, 0), (68, 1), (69, 0), (70, 0), (70, 1), (71, 0), (72, 0), (74, 0), (75, 1), (76, 0), (76, 1), (77, 0), (77, 1), (78, 0), (78, 1), (80, 0), (80, 1), (82, 0), (82, 1), (84, 0), (85, 0), (86, 0), (86, 1), (88, 0), (90, 0), (91, 1), (92, 0), (92, 1), (93, 0), (94, 0), (95, 0), (96, 0), (98, 0), (99, 1), (100, 0), (100, 1), (101, 0), (101, 1), (103, 0), (103, 1), (105, 0), (105, 1), (107, 0), (108, 0), (109, 0), (109, 1), (112, 0), (113, 0), (114, 0), (116, 0), (117, 0), (117, 1), (118, 0), (118, 1), (121, 0), (124, 1), (125, 0), (126, 0), (128, 0), (128, 1), (130, 0), (130, 1), (135, 0), (136, 0), (137, 0), (139, 0), (142, 1), (143, 0), (144, 1), (148, 1), (150, 0), (150, 1), (151, 1), (158, 1)]

@[expose] def hTbl : List (List ℕ) :=
  [[1, 2], [3, 4], [5, 0], [6, 7], [8, 1], [9, 10], [11, 12], [13, 3], [14, 15], [16, 17], [18, 5], [19, 20], [21, 6], [22, 23], [24, 25], [2, 8], [26, 27], [28, 9], [29, 30], [30, 31], [32, 11], [33, 34], [35, 36], [4, 13], [37, 38], [39, 14], [40, 41], [42, 16], [43, 44], [45, 46], [0, 18], [47, 19], [48, 49], [50, 51], [7, 21], [52, 53], [54, 22], [55, 56], [57, 24], [58, 40], [15, 39], [59, 26], [60, 61], [62, 63], [10, 28], [64, 65], [31, 29], [66, 67], [68, 69], [12, 32], [70, 71], [72, 33], [73, 74], [75, 35], [76, 55], [23, 54], [77, 37], [78, 79], [80, 81], [82, 83], [84, 85], [17, 42], [86, 87], [88, 43], [89, 90], [91, 45], [92, 93], [20, 47], [94, 95], [96, 48], [97, 98], [99, 50], [100, 73], [34, 72], [101, 52], [63, 102], [103, 104], [105, 106], [107, 108], [25, 57], [109, 110], [41, 58], [111, 112], [27, 59], [113, 94], [114, 60], [115, 116], [102, 62], [117, 89], [44, 88], [118, 64], [108, 119], [120, 121], [122, 66], [123, 84], [124, 68], [125, 97], [49, 96], [126, 70], [81, 127], [128, 129], [130, 131], [36, 75], [132, 133], [56, 76], [134, 135], [38, 77], [136, 120], [137, 78], [138, 139], [127, 80], [71, 126], [140, 82], [141, 134], [142, 115], [61, 114], [143, 86], [144, 145], [146, 147], [46, 91], [119, 107], [148, 92], [85, 123], [67, 122], [104, 149], [150, 146], [151, 111], [51, 99], [152, 153], [74, 100], [154, 155], [53, 101], [87, 143], [149, 103], [95, 113], [156, 105], [157, 154], [158, 138], [79, 137], [159, 109], [135, 141], [83, 140], [153, 160], [161, 132], [131, 162], [90, 117], [98, 125], [65, 118], [129, 163], [69, 124], [164, 165], [145, 166], [110, 159], [163, 128], [121, 136], [162, 130], [155, 157], [106, 156], [165, 167], [160, 152], [116, 142], [167, 164], [166, 144], [93, 148], [133, 161], [147, 150], [112, 151], [139, 158]]

@[expose] def dGenC : List (List ℕ) := [[2, 5, 4, 1, 7, 6, 3, 0], [1, 0, 3, 2, 6, 7, 4, 5]]

@[expose] def dTree : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0), (3, 1)]

@[expose] def dTbl : List (List ℕ) :=
  [[1, 2], [3, 4], [5, 0], [6, 7], [2, 1], [7, 6], [0, 5], [4, 3]]

@[expose] def dLit : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7], [2, 5, 4, 1, 7, 6, 3, 0], [1, 0, 3, 2, 6, 7, 4, 5], [4, 6, 7, 5, 0, 3, 1, 2], [5, 2, 1, 4, 3, 0, 7, 6], [3, 7, 6, 0, 5, 4, 2, 1], [7, 3, 0, 6, 2, 1, 5, 4], [6, 4, 5, 7, 1, 2, 0, 3]]

@[expose] def eGenC : List (List ℕ) := [[2, 5, 4, 1, 7, 6, 3, 0], [1, 0, 3, 2, 6, 7, 4, 5], [7, 1, 4, 5, 2, 3, 6, 0]]

@[expose] def eTree : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 2), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 2), (9, 1)]

@[expose] def eTbl : List (List ℕ) :=
  [[1, 2, 3], [4, 5, 6], [7, 0, 8], [9, 10, 0], [11, 12, 13], [2, 1, 14], [3, 8, 1], [12, 11, 10], [14, 6, 2], [13, 15, 11], [8, 3, 7], [0, 7, 9], [5, 4, 15], [6, 14, 4], [15, 13, 5], [10, 9, 12]]

@[expose] def eLit : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7], [2, 5, 4, 1, 7, 6, 3, 0], [1, 0, 3, 2, 6, 7, 4, 5], [7, 1, 4, 5, 2, 3, 6, 0], [4, 6, 7, 5, 0, 3, 1, 2], [5, 2, 1, 4, 3, 0, 7, 6], [0, 5, 7, 6, 4, 1, 3, 2], [3, 7, 6, 0, 5, 4, 2, 1], [5, 0, 6, 7, 3, 2, 4, 1], [4, 3, 2, 1, 0, 6, 5, 7], [1, 7, 5, 4, 6, 0, 2, 3], [7, 3, 0, 6, 2, 1, 5, 4], [6, 4, 5, 7, 1, 2, 0, 3], [2, 6, 0, 3, 7, 5, 1, 4], [6, 2, 3, 0, 1, 4, 7, 5], [3, 4, 1, 2, 5, 7, 0, 6]]

theorem h_gens : [NFF7.g1, pb].map (codeN 8) = hGenC := by decide

theorem d_gens : [pu, pv].map (codeN 8) = dGenC := by decide

theorem e_gens : [pu, pv, NFF7.g2].map (codeN 8) = eGenC := by decide

theorem h_tbl : Core.tblCheckC (List.range 8) hGenC (Core.buildCodes (List.range 8) hGenC hTree)
    hTbl = true := by
  decide +kernel

theorem h_nodup : (Core.buildCodes (List.range 8) hGenC hTree).Nodup := by decide +kernel

theorem h_length : (Core.buildCodes (List.range 8) hGenC hTree).length = 168 := by decide +kernel

theorem d_build : dLit = Core.buildCodes (List.range 8) dGenC dTree := by decide +kernel

theorem d_tbl : Core.tblCheckC (List.range 8) dGenC (Core.buildCodes (List.range 8) dGenC dTree)
    dTbl = true := by
  decide +kernel

theorem d_nodup : (Core.buildCodes (List.range 8) dGenC dTree).Nodup := by decide +kernel

theorem d_length : (Core.buildCodes (List.range 8) dGenC dTree).length = 8 := by decide +kernel

theorem e_build : eLit = Core.buildCodes (List.range 8) eGenC eTree := by decide +kernel

theorem e_tbl : Core.tblCheckC (List.range 8) eGenC (Core.buildCodes (List.range 8) eGenC eTree)
    eTbl = true := by
  decide +kernel

theorem pu_mem_h : codeN 8 pu ∈ Core.buildCodes (List.range 8) hGenC hTree := by decide +kernel

theorem pv_mem_h : codeN 8 pv ∈ Core.buildCodes (List.range 8) hGenC hTree := by decide +kernel

theorem norm_check : ∀ c ∈ NFF7.gLit, (∃ d ∈ dLit, Core.cmul c (codeN 8 pu) = Core.cmul d c) →
    (∃ d ∈ dLit, Core.cmul c (codeN 8 pv) = Core.cmul d c) → c ∈ eLit := by
  decide +kernel

theorem split_check : ∀ c ∈ eLit, c ∈ dLit ∨ ∃ d ∈ dLit, c = Core.cmul d (codeN 8 NFF7.g2) := by
  decide +kernel

theorem pw_mem_g : codeN 8 pw ∈ NFF7.gLit := by decide +kernel

theorem pw_sq : pb = pw * pw := by decide

theorem g1_sq : NFF7.g1 = NFF7.g1 ^ 4 * NFF7.g1 ^ 4 := by decide

end CFSG.LocalAnalysis.WeakClosure81.NGM
