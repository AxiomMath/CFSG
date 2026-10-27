module

public import CFSG.Quasithin.Background.HZCoc24Gen

public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk

@[expose] def gaArr : Array ℕ :=
  #[0, 1, 17, 20, 5, 16, 4, 21, 2, 8, 13, 6, 14, 22, 18, 15, 3, 12, 9, 7, 11, 23, 19, 10]

@[expose] def gaInv : Array ℕ :=
  #[0, 1, 8, 16, 6, 4, 11, 19, 9, 18, 23, 20, 17, 10, 12, 15, 5, 2, 14, 22, 3, 7, 13, 21]

@[expose] def gbArr : Array ℕ :=
  #[0, 1, 19, 15, 20, 8, 5, 3, 11, 12, 18, 9, 14, 21, 16, 23, 6, 2, 10, 22, 13, 17, 4, 7]

@[expose] def gbInv : Array ℕ :=
  #[0, 1, 17, 7, 22, 6, 16, 23, 5, 11, 18, 8, 9, 20, 12, 3, 14, 21, 10, 2, 4, 13, 19, 15]

theorem g_ok : InvPairOK 24 gaArr gaInv = true ∧ InvPairOK 24 gbArr gbInv = true ∧
    autArrOK gaArr gaInv = true ∧ autArrOK gbArr gbInv = true ∧
    gaArr[0]! = 0 ∧ gaArr[1]! = 1 ∧ gbArr[0]! = 0 ∧ gbArr[1]! = 1 := by
  decide +kernel

@[expose] def lxArr : Array ℕ :=
  #[0, 1, 5, 7, 6, 2, 3, 4, 10, 19, 9, 16, 15, 22, 12, 21, 20, 13, 23, 14, 17, 8, 18, 11]

@[expose] def lxInv : Array ℕ :=
  #[0, 1, 5, 6, 7, 2, 4, 3, 21, 10, 8, 23, 14, 17, 19, 12, 11, 20, 22, 9, 16, 15, 13, 18]

@[expose] def lyArr : Array ℕ :=
  #[0, 1, 6, 7, 3, 2, 5, 4, 8, 9, 14, 15, 11, 10, 13, 12, 20, 21, 18, 19, 23, 22, 17, 16]

@[expose] def lyInv : Array ℕ :=
  #[0, 1, 5, 4, 7, 6, 2, 3, 8, 9, 13, 12, 15, 14, 10, 11, 23, 22, 18, 19, 16, 17, 21, 20]

theorem l_ok : InvPairOK 24 lxArr lxInv = true ∧ InvPairOK 24 lyArr lyInv = true ∧
    autArrOK lxArr lxInv = true ∧ autArrOK lyArr lyInv = true ∧
    lxArr[0]! = 0 ∧ lxArr[1]! = 1 ∧ lyArr[0]! = 0 ∧ lyArr[1]! = 1 := by
  decide +kernel

theorem l_fix : actC10 lxArr 1 = 1 ∧ actC10 lyArr 1 = 1 := by
  decide +kernel

theorem l_oct : ∀ i < 24, (lxArr[i]! < 8 ↔ i < 8) ∧ (lyArr[i]! < 8 ↔ i < 8) := by
  decide +kernel

theorem l_hex : ∀ i < 6, lxArr[i + 2]! = Coc24.colXArr[i]! + 2 ∧
    lyArr[i + 2]! = Coc24.colYArr[i]! + 2 := by
  decide +kernel

@[expose] def orbAct (g m : ℕ) : ℕ := actC10 (if g = 0 then gaArr else gbArr) m

@[expose] def orbTree0 : List (ℕ × ℕ × ℕ) := [
    (86, 1, 0), (109, 1, 1), (876, 86, 0), (189, 86, 1), (1015, 109, 0), (786, 109, 1),
    (679, 876, 0), (338, 876, 1), (821, 189, 0), (880, 189, 1), (928, 1015, 0), (416, 1015, 1),
    (688, 786, 0), (721, 786, 1), (814, 679, 0), (216, 679, 1), (51, 338, 0), (212, 821, 0),
    (318, 821, 1), (88, 880, 0), (274, 880, 1), (154, 928, 0), (368, 928, 1), (732, 416, 0),
    (148, 416, 1), (209, 688, 0), (81, 688, 1), (722, 721, 0), (491, 721, 1), (735, 814, 0),
    (799, 814, 1), (297, 216, 0), (287, 51, 1), (221, 212, 0), (122, 212, 1), (914, 318, 0),
    (19, 318, 1), (549, 88, 0), (246, 274, 0), (337, 154, 0), (159, 154, 1), (542, 368, 0),
    (24, 148, 0), (35, 148, 1), (15, 209, 1), (920, 81, 0), (569, 722, 0), (793, 491, 0),
    (4, 491, 1), (923, 735, 0), (343, 735, 1), (20, 799, 1), (340, 287, 0), (496, 287, 1),
    (352, 221, 0), (8, 122, 0), (444, 914, 0), (2, 914, 1), (992, 19, 0), (145, 19, 1)]

@[expose] def orbTree1 : List (ℕ × ℕ × ℕ) := [
    (31, 549, 1), (752, 246, 0), (277, 337, 1), (280, 159, 0), (234, 159, 1), (944, 542, 1),
    (736, 24, 0), (635, 35, 0), (166, 920, 1), (608, 569, 0), (95, 569, 1), (536, 793, 1),
    (788, 20, 0), (532, 2, 1), (913, 280, 1), (530, 635, 1)]

@[expose] def orbTree : List (ℕ × ℕ × ℕ) :=
  orbTree0 ++ orbTree1

theorem orbTree_ok : treeB orbAct orbTree (1 <<< 1) = true := by
  decide +kernel

theorem orbTree_length : orbTree.length = 76 := by
  decide +kernel

theorem orbTree_lt : ∀ e ∈ orbTree, e.1 < 2 ^ 10 := by
  decide +kernel

theorem ko_fix : ∀ t < 16, actC10 (koArr t) 1 = 1 := by
  decide +kernel

@[expose] def koWords : List (List ℕ) := [
    [], [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [1, 1, 0, 0, 0, 0, 1],
    [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1],
    [0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], [1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    [1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1]]

@[expose] def koWord (t : ℕ) : List ℕ := koWords.getD t []

theorem koWord_ok : ∀ t < 16, wArr [lxArr, lyArr] (koWord t) = koArr t := by
  decide +kernel

@[expose] def mxCols : List ℕ := [9, 3, 5, 14]

@[expose] def myCols : List ℕ := [1, 6, 3, 12]

theorem ko_conj : ∀ t < 16, cArr lxArr (cArr (koArr t) lxInv) = koArr (actM mxCols t) ∧
    cArr lyArr (cArr (koArr t) lyInv) = koArr (actM myCols t) := by
  decide +kernel

theorem actM_ko_lt : ∀ t < 16, actM mxCols t < 16 ∧ actM myCols t < 16 := by
  decide +kernel

@[expose] def c0Arr : Array ℕ := cArr (cArr lxArr lyArr) (cArr lxInv lyInv)

@[expose] def c2Arr : Array ℕ :=
  cArr (cArr (cArr lxArr lxArr) lyArr) (cArr (cArr lxInv lxInv) lyInv)

@[expose] def xWord : List ℕ := [1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0]

@[expose] def yWord : List ℕ := [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0]

theorem perfect_words :
    wArr [c0Arr, c2Arr] xWord = lxArr ∧ wArr [c0Arr, c2Arr] yWord = lyArr := by
  decide +kernel

@[expose] def kcArr (i : ℕ) : Array ℕ :=
  if i < 4 then cArr (cArr (koArr (2 ^ i)) lxArr) (cArr (koArr (2 ^ i)) lxInv)
  else cArr (cArr (koArr (2 ^ (i - 4))) lyArr) (cArr (koArr (2 ^ (i - 4))) lyInv)

@[expose] def koComms : List (List ℕ) := [
    [], [1], [3, 5], [1, 3, 5], [5], [1, 5], [3], [1, 3], [0], [0, 1], [0, 3, 5], [0, 1, 3, 5],
    [0, 5], [0, 1, 5], [0, 3], [0, 1, 3]]

@[expose] def koComm (t : ℕ) : List ℕ := koComms.getD t []

theorem koComm_ok : ∀ t < 16, wArr ((List.range 8).map kcArr) (koComm t) = koArr t := by
  decide +kernel

@[expose] def w0Basis : List ℕ := [7, 266, 12, 1, 518]

theorem w0Basis_eq : w0Basis = [
      actC10 (koArr 1) (2 ^ 4) ^^^ 2 ^ 4, actC10 (koArr 1) (2 ^ 5) ^^^ 2 ^ 5,
      actC10 (koArr 1) (2 ^ 7) ^^^ 2 ^ 7, actC10 (koArr 1) (2 ^ 9) ^^^ 2 ^ 9,
      actC10 (koArr 2) (2 ^ 5) ^^^ 2 ^ 5] := by
  decide +kernel

theorem w0_nodup : nodupB (combos w0Basis) 0 = true := by
  decide +kernel

theorem w0_lt : ∀ a ∈ w0Basis, a < 2 ^ 10 := by
  decide +kernel

theorem z0_mem_w0 : 1 ∈ combos w0Basis := by
  decide +kernel

theorem ko_comm_mem_w0 :
    ∀ t < 16, ∀ j < 10, actC10 (koArr t) (2 ^ j) ^^^ 2 ^ j ∈ combos w0Basis := by
  decide +kernel

@[expose] def lAct (g m : ℕ) : ℕ := actC10 (if g = 0 then lxArr else lyArr) m

@[expose] def irrWData : List (ℕ × List (ℕ × ℕ)) := [
    (6, [(0, 0), (0, 2), (1, 2)]), (7, [(0, 0), (0, 2), (1, 2)]), (10, [(0, 0), (1, 0), (0, 3)]),
    (11, [(0, 0), (1, 0), (0, 3)]), (12, [(0, 0), (1, 0), (0, 2)]),
    (13, [(0, 0), (1, 0), (0, 2)]), (256, [(0, 0), (1, 0), (1, 2)]),
    (257, [(0, 0), (1, 0), (1, 2)]), (262, [(0, 0), (1, 0), (0, 2)]),
    (263, [(0, 0), (1, 0), (0, 2)]), (266, [(1, 0), (0, 2), (1, 2)]),
    (267, [(1, 0), (0, 2), (1, 2)]), (268, [(0, 0), (1, 0), (0, 2)]),
    (269, [(0, 0), (1, 0), (0, 2)]), (512, [(0, 0), (1, 0), (1, 2)]),
    (513, [(0, 0), (1, 0), (1, 2)]), (518, [(0, 0), (1, 0), (1, 3)]),
    (519, [(0, 0), (1, 0), (1, 3)]), (522, [(0, 0), (1, 0), (1, 2)]),
    (523, [(0, 0), (1, 0), (1, 2)]), (524, [(0, 0), (1, 0), (0, 3)]),
    (525, [(0, 0), (1, 0), (0, 3)]), (768, [(0, 0), (0, 2), (1, 2)]),
    (769, [(0, 0), (0, 2), (1, 2)]), (774, [(0, 0), (0, 2), (1, 2)]),
    (775, [(0, 0), (0, 2), (1, 2)]), (778, [(0, 0), (1, 0), (1, 2)]),
    (779, [(0, 0), (1, 0), (1, 2)]), (780, [(0, 0), (1, 0), (0, 2)]),
    (781, [(0, 0), (1, 0), (0, 2)])]

theorem irrW_ok : ∀ e ∈ irrWData, nodupB (combos (derivB lAct [e.1, 1] e.2)) 0 = true ∧
    (derivB lAct [e.1, 1] e.2).length = 5 := by
  decide +kernel

theorem irrW_cover : ∀ m ∈ combos w0Basis, m ≠ 0 → m ≠ 1 → m ∈ irrWData.map Prod.fst := by
  decide +kernel

@[expose] def koAct (g c : ℕ) : ℕ := actM (if g = 0 then mxCols else myCols) c

@[expose] def irrKData : List (ℕ × List (ℕ × ℕ)) := [
    (1, [(0, 0), (0, 1), (1, 1)]), (2, [(0, 0), (1, 0), (0, 1)]), (3, [(0, 0), (1, 0), (0, 2)]),
    (4, [(0, 0), (1, 0), (0, 1)]), (5, [(0, 0), (1, 0), (1, 1)]), (6, [(1, 0), (0, 1), (1, 1)]),
    (7, [(0, 0), (1, 0), (0, 1)]), (8, [(0, 0), (1, 0), (1, 1)]), (9, [(0, 0), (1, 0), (0, 1)]),
    (10, [(0, 0), (0, 1), (1, 1)]), (11, [(0, 0), (0, 1), (1, 1)]),
    (12, [(0, 0), (1, 0), (0, 2)]), (13, [(0, 0), (1, 0), (1, 1)]),
    (14, [(0, 0), (1, 0), (1, 1)]), (15, [(0, 0), (1, 0), (1, 2)])]

theorem irrK_ok : ∀ e ∈ irrKData, ∀ c < 16, c ∈ combos (derivB koAct [e.1] e.2) := by
  decide +kernel

theorem irrK_cover : ∀ c < 16, c ≠ 0 → c ∈ irrKData.map Prod.fst := by
  decide +kernel

@[expose] def cvData : List (ℕ × ℕ) := [
    (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 5)]

theorem cv_ok : nodupB (combos (cvData.map fun e => lAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2)) 0 = true ∧
    cvData.length = 10 := by
  decide +kernel

end CFSG.Quasithin.H.Code22
