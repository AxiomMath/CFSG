module

public import CFSG.Quasithin.Background.HModChk
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Fischer Matrix CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H13.Ch9.L34M

@[expose] def fc (n : ℕ) : F4 := ⟨⟨n % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def mc (l : List ℕ) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of fun i j => fc (l.getD (3 * i + j) 0)

@[expose] def wM (ms : List (Matrix (Fin 3) (Fin 3) F4)) : List ℕ → Matrix (Fin 3) (Fin 3) F4
  | [] => 1
  | i :: w => ms.getD i 1 * wM ms w

@[expose] def mcode (A : Matrix (Fin 3) (Fin 3) F4) : List ℕ :=
  [(A 0 0).code.val, (A 0 1).code.val, (A 0 2).code.val, (A 1 0).code.val, (A 1 1).code.val,
    (A 1 2).code.val, (A 2 0).code.val, (A 2 1).code.val, (A 2 2).code.val]

theorem f4_eq_of_code {x y : F4} (h : x.code.val = y.code.val) : x = y := by
  cases x
  cases y
  congr
  exact Fin.ext h

theorem mcode_injective {A B : Matrix (Fin 3) (Fin 3) F4} (h : mcode A = mcode B) : A = B := by
  simp only [mcode, List.cons.injEq, and_true] at h
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := h
  ext i j
  fin_cases i <;> fin_cases j
  · exact f4_eq_of_code h00
  · exact f4_eq_of_code h01
  · exact f4_eq_of_code h02
  · exact f4_eq_of_code h10
  · exact f4_eq_of_code h11
  · exact f4_eq_of_code h12
  · exact f4_eq_of_code h20
  · exact f4_eq_of_code h21
  · exact f4_eq_of_code h22

@[expose] def xM : Matrix (Fin 3) (Fin 3) F4 := mc [2, 3, 0, 0, 0, 2, 0, 2, 0]

@[expose] def xMi : Matrix (Fin 3) (Fin 3) F4 := mc [3, 0, 1, 0, 0, 3, 0, 3, 0]

@[expose] def yM : Matrix (Fin 3) (Fin 3) F4 := mc [2, 3, 0, 0, 1, 3, 0, 2, 2]

@[expose] def yMi : Matrix (Fin 3) (Fin 3) F4 := mc [3, 1, 2, 0, 3, 1, 0, 3, 2]

theorem xy_inv_code : mcode (xM * xMi) = mcode 1 ∧ mcode (xMi * xM) = mcode 1 ∧
    mcode (yM * yMi) = mcode 1 ∧ mcode (yMi * yM) = mcode 1 := by
  decide +kernel

theorem x_inv : xM * xMi = 1 ∧ xMi * xM = 1 :=
  ⟨mcode_injective xy_inv_code.1, mcode_injective xy_inv_code.2.1⟩

theorem y_inv : yM * yMi = 1 ∧ yMi * yM = 1 :=
  ⟨mcode_injective xy_inv_code.2.2.1, mcode_injective xy_inv_code.2.2.2⟩

theorem det_xM : xM.det = 1 := by
  rw [Matrix.det_fin_three]
  exact f4_eq_of_code (by decide +kernel)

theorem det_yM : yM.det = 1 := by
  rw [Matrix.det_fin_three]
  exact f4_eq_of_code (by decide +kernel)

@[expose] def colsX : List ℕ := [1, 69, 2, 33, 64, 8, 16, 144, 408]

@[expose] def colsY : List ℕ := [1, 479, 262, 49, 88, 56, 72, 202, 118]

theorem cols_x : cols xM = colsX := by
  decide +kernel

theorem cols_y : cols yM = colsY := by
  decide +kernel

theorem xy_fix : actM colsX 1 = 1 ∧ actM colsY 1 = 1 := by
  decide +kernel

@[expose] def oMs : List (Matrix (Fin 3) (Fin 3) F4) := [
    mc [1, 0, 0, 1, 1, 0, 0, 0, 1], mc [0, 0, 1, 1, 0, 0, 0, 1, 0],
    mc [2, 0, 0, 0, 3, 0, 0, 0, 1]]

@[expose] def oMis : List (Matrix (Fin 3) (Fin 3) F4) := [
    mc [1, 0, 0, 1, 1, 0, 0, 0, 1], mc [0, 1, 0, 0, 0, 1, 1, 0, 0],
    mc [3, 0, 0, 0, 2, 0, 0, 0, 1]]

theorem o_inv_code : ∀ i < 3, mcode (oMs.getD i 1 * oMis.getD i 1) = mcode 1 ∧
    mcode (oMis.getD i 1 * oMs.getD i 1) = mcode 1 := by
  decide +kernel

theorem o_inv (i : ℕ) (hi : i < 3) :
    oMs.getD i 1 * oMis.getD i 1 = 1 ∧ oMis.getD i 1 * oMs.getD i 1 = 1 :=
  ⟨mcode_injective (o_inv_code i hi).1, mcode_injective (o_inv_code i hi).2⟩

theorem det_oM0 : (oMs.getD 0 1).det = 1 := by
  rw [Matrix.det_fin_three]
  exact f4_eq_of_code (by decide +kernel)

theorem det_oM1 : (oMs.getD 1 1).det = 1 := by
  rw [Matrix.det_fin_three]
  exact f4_eq_of_code (by decide +kernel)

theorem det_oM2 : (oMs.getD 2 1).det = 1 := by
  rw [Matrix.det_fin_three]
  exact f4_eq_of_code (by decide +kernel)

@[expose] def colsO : List (List ℕ) := [
    [11, 2, 4, 8, 18, 160, 320, 128, 256], [2, 4, 1, 128, 256, 8, 24, 32, 96],
    [1, 2, 4, 24, 8, 64, 96, 384, 128]]

theorem cols_o : ∀ i < 3, cols (oMs.getD i 1) = colsO.getD i [] := by
  decide +kernel

@[expose] def orbAct (g m : ℕ) : ℕ := actM (colsO.getD (g % 3) []) m

@[expose] def orbTree : List (ℕ × ℕ × ℕ) := [
    (11, 1, 0), (2, 1, 1), (134, 11, 1), (27, 11, 2), (4, 2, 1), (37, 134, 1), (390, 134, 2),
    (19, 27, 0), (175, 37, 0), (69, 37, 2), (262, 390, 2), (479, 175, 2), (335, 69, 0),
    (101, 69, 2), (215, 479, 0), (375, 479, 2), (255, 335, 1), (495, 101, 0), (319, 215, 1),
    (439, 255, 1)]

theorem orbTree_ok : treeB orbAct orbTree (1 <<< 1) = true := by
  decide +kernel

theorem orbTree_length : orbTree.length = 20 := by
  decide +kernel

theorem orbTree_lt : ∀ e ∈ orbTree, e.1 < 2 ^ 9 := by
  decide +kernel

@[expose] def uM (t : ℕ) : Matrix (Fin 3) (Fin 3) F4 := um (fc t) (fc (t / 4)) 0

theorem uM_mul_code : ∀ t < 16, ∀ s < 16, mcode (uM t * uM s) = mcode (uM (t ^^^ s)) := by
  decide +kernel

theorem uM_mul (t : ℕ) (ht : t < 16) (s : ℕ) (hs : s < 16) : uM t * uM s = uM (t ^^^ s) :=
  mcode_injective (uM_mul_code t ht s hs)

theorem uM_zero : uM 0 = 1 :=
  mcode_injective (by decide +kernel)

@[expose] def colsU : List (List ℕ) := [
    [1, 2, 4, 8, 16, 32, 64, 128, 256], [1, 11, 4, 8, 17, 32, 64, 160, 320],
    [1, 19, 4, 9, 16, 32, 64, 192, 352], [1, 27, 4, 9, 17, 32, 64, 224, 288],
    [1, 2, 37, 8, 16, 32, 65, 136, 280], [1, 11, 37, 8, 17, 32, 65, 168, 345],
    [1, 19, 37, 9, 16, 32, 65, 201, 377], [1, 27, 37, 9, 17, 32, 65, 233, 312],
    [1, 2, 69, 8, 16, 33, 64, 144, 264], [1, 11, 69, 8, 17, 33, 64, 177, 328],
    [1, 19, 69, 9, 16, 33, 64, 208, 361], [1, 27, 69, 9, 17, 33, 64, 241, 297],
    [1, 2, 101, 8, 16, 33, 65, 152, 272], [1, 11, 101, 8, 17, 33, 65, 185, 337],
    [1, 19, 101, 9, 16, 33, 65, 217, 368], [1, 27, 101, 9, 17, 33, 65, 248, 305]]

theorem cols_u : ∀ t < 16, cols (uM t) = colsU.getD t [] := by
  decide +kernel

theorem colsU_nodup : ((List.range 16).map fun t => colsU.getD t []).Nodup := by
  decide +kernel

theorem u_fix1 : ∀ t < 16, actM (colsU.getD t []) 1 = 1 := by
  decide +kernel

theorem u_fix : ∀ m < 512, actM (colsU.getD 1 []) m = m ∧ actM (colsU.getD 2 []) m = m ∧
    actM (colsU.getD 4 []) m = m ∧ actM (colsU.getD 8 []) m = m → m = 0 ∨ m = 1 := by
  decide +kernel

@[expose] def uWords : List (List ℕ) := [
    [], [1, 1, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 1, 1, 1, 1, 0, 0], [1, 1, 1, 0, 0, 1, 1],
    [1, 1, 1, 0, 0, 1, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0, 1, 1], [1, 1, 0, 0, 1, 1, 1],
    [1, 1, 1, 1, 0, 0, 1], [1, 0, 0, 1, 1, 1, 1], [1, 1, 1, 0, 0, 1, 1, 0, 0], [0, 0],
    [1, 0, 0, 1, 1, 0, 0, 1, 1], [1, 1, 0, 0, 1, 1, 1, 0, 0], [1, 1, 1, 1, 0, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 0, 1, 1, 1], [1, 0, 0, 1, 1, 1, 0, 0, 1]]

@[expose] def uWord (t : ℕ) : List ℕ := uWords.getD t []

theorem uWord_ok : ∀ t < 16, cols (wM [xM, yM] (uWord t)) = colsU.getD t [] := by
  decide +kernel

@[expose] def mxCols : List ℕ := [4, 8, 1, 2]

@[expose] def myCols : List ℕ := [9, 14, 13, 6]

theorem u_conj_code : ∀ t < 16, mcode (xM * uM t * xMi) = mcode (uM (actM mxCols t)) ∧
    mcode (yM * uM t * yMi) = mcode (uM (actM myCols t)) := by
  decide +kernel

theorem u_conj (t : ℕ) (ht : t < 16) : xM * uM t * xMi = uM (actM mxCols t) ∧
    yM * uM t * yMi = uM (actM myCols t) :=
  ⟨mcode_injective (u_conj_code t ht).1, mcode_injective (u_conj_code t ht).2⟩

theorem actM_u_lt : ∀ t < 16, actM mxCols t < 16 ∧ actM myCols t < 16 := by
  decide +kernel

@[expose] def c0M : Matrix (Fin 3) (Fin 3) F4 := xM * yM * xMi * yMi

@[expose] def c2M : Matrix (Fin 3) (Fin 3) F4 := xM * (yM * yM) * xMi * (yMi * yMi)

@[expose] def xWord : List ℕ := [1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0]

@[expose] def yWord : List ℕ := [1, 1, 0, 0, 1, 1, 0, 1, 1, 0]

theorem perfect_words : cols (wM [c0M, c2M] xWord) = colsX ∧
    cols (wM [c0M, c2M] yWord) = colsY := by
  decide +kernel

@[expose] def kcM (i : ℕ) : Matrix (Fin 3) (Fin 3) F4 :=
  if i < 4 then uM (2 ^ i) * xM * uM (2 ^ i) * xMi
  else uM (2 ^ (i - 4)) * yM * uM (2 ^ (i - 4)) * yMi

@[expose] def koComms : List (List ℕ) := [
    [], [0, 4, 5], [1, 4], [0, 1, 5], [4, 5], [0], [1, 5], [0, 1, 4], [4], [0, 5], [1],
    [0, 1, 4, 5], [5], [0, 4], [1, 4, 5], [0, 1]]

@[expose] def koComm (t : ℕ) : List ℕ := koComms.getD t []

theorem koComm_code : ∀ t < 16, mcode (wM ((List.range 8).map kcM) (koComm t)) = mcode (uM t) := by
  decide +kernel

theorem koComm_ok (t : ℕ) (ht : t < 16) : wM ((List.range 8).map kcM) (koComm t) = uM t :=
  mcode_injective (koComm_code t ht)

@[expose] def w0Basis : List ℕ := [9, 1, 32, 64, 17]

theorem w0Basis_eq : w0Basis = [
      actM (colsU.getD 1 []) (2 ^ 1) ^^^ 2 ^ 1, actM (colsU.getD 1 []) (2 ^ 4) ^^^ 2 ^ 4,
      actM (colsU.getD 1 []) (2 ^ 7) ^^^ 2 ^ 7, actM (colsU.getD 1 []) (2 ^ 8) ^^^ 2 ^ 8,
      actM (colsU.getD 2 []) (2 ^ 1) ^^^ 2 ^ 1] := by
  decide +kernel

theorem w0_nodup : nodupB (combos w0Basis) 0 = true := by
  decide +kernel

theorem w0_lt : ∀ a ∈ w0Basis, a < 2 ^ 9 := by
  decide +kernel

theorem z0_mem_w0 : 1 ∈ combos w0Basis := by
  decide +kernel

theorem u_comm_mem_w0 :
    ∀ t < 16, ∀ j < 9, actM (colsU.getD t []) (2 ^ j) ^^^ 2 ^ j ∈ combos w0Basis := by
  decide +kernel

@[expose] def lAct (g m : ℕ) : ℕ := actM (if g = 0 then colsX else colsY) m

@[expose] def irrWData : List (ℕ × List (ℕ × ℕ)) := [
    (8, [(0, 0), (1, 0), (0, 3)]), (9, [(0, 0), (1, 0), (0, 3)]), (16, [(0, 0), (1, 0), (0, 3)]),
    (17, [(0, 0), (1, 0), (0, 3)]), (24, [(0, 0), (1, 0), (0, 3)]),
    (25, [(0, 0), (1, 0), (0, 3)]), (32, [(0, 0), (1, 0), (0, 3)]),
    (33, [(0, 0), (1, 0), (0, 3)]), (40, [(1, 0), (1, 2), (0, 3)]),
    (41, [(1, 0), (1, 2), (0, 3)]), (48, [(0, 0), (1, 0), (1, 3)]),
    (49, [(0, 0), (1, 0), (1, 3)]), (56, [(0, 0), (1, 2), (1, 3)]),
    (57, [(0, 0), (1, 2), (1, 3)]), (64, [(0, 0), (1, 0), (0, 3)]),
    (65, [(0, 0), (1, 0), (0, 3)]), (72, [(0, 0), (1, 2), (1, 3)]),
    (73, [(0, 0), (1, 2), (1, 3)]), (80, [(1, 0), (1, 2), (0, 3)]),
    (81, [(1, 0), (1, 2), (0, 3)]), (88, [(0, 0), (1, 0), (1, 3)]),
    (89, [(0, 0), (1, 0), (1, 3)]), (96, [(0, 0), (1, 0), (0, 3)]),
    (97, [(0, 0), (1, 0), (0, 3)]), (104, [(0, 0), (1, 0), (1, 3)]),
    (105, [(0, 0), (1, 0), (1, 3)]), (112, [(0, 0), (1, 2), (1, 3)]),
    (113, [(0, 0), (1, 2), (1, 3)]), (120, [(1, 0), (1, 2), (0, 3)]),
    (121, [(1, 0), (1, 2), (0, 3)])]

theorem irrW_ok : ∀ e ∈ irrWData, nodupB (combos (derivB lAct [e.1, 1] e.2)) 0 = true ∧
    (derivB lAct [e.1, 1] e.2).length = 5 := by
  decide +kernel

theorem irrW_cover : ∀ m ∈ combos w0Basis, m ≠ 0 → m ≠ 1 → m ∈ irrWData.map Prod.fst := by
  decide +kernel

@[expose] def koAct (g c : ℕ) : ℕ := actM (if g = 0 then mxCols else myCols) c

@[expose] def irrKData : List (ℕ × List (ℕ × ℕ)) := [
    (1, [(0, 0), (1, 0), (0, 2)]), (2, [(0, 0), (1, 0), (0, 2)]), (3, [(0, 0), (1, 0), (0, 2)]),
    (4, [(0, 0), (1, 0), (0, 2)]), (5, [(1, 0), (1, 1), (0, 2)]), (6, [(0, 0), (1, 0), (1, 2)]),
    (7, [(0, 0), (1, 1), (1, 2)]), (8, [(0, 0), (1, 0), (0, 2)]), (9, [(0, 0), (1, 1), (1, 2)]),
    (10, [(1, 0), (1, 1), (0, 2)]), (11, [(0, 0), (1, 0), (1, 2)]),
    (12, [(0, 0), (1, 0), (0, 2)]), (13, [(0, 0), (1, 0), (1, 2)]),
    (14, [(0, 0), (1, 1), (1, 2)]), (15, [(1, 0), (1, 1), (0, 2)])]

theorem irrK_ok : ∀ e ∈ irrKData, ∀ c < 16, c ∈ combos (derivB koAct [e.1] e.2) := by
  decide +kernel

theorem irrK_cover : ∀ c < 16, c ≠ 0 → c ∈ irrKData.map Prod.fst := by
  decide +kernel

@[expose] def cvData : List (ℕ × ℕ) := [
    (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 8), (1, 1), (1, 4), (1, 7)]

theorem cv_ok : nodupB (combos (cvData.map fun e => lAct e.1 (2 ^ e.2) ^^^ 2 ^ e.2)) 0 = true ∧
    cvData.length = 9 := by
  decide +kernel

@[expose] def sM (p : ℕ) : Matrix (Fin 3) (Fin 3) F4 := um (fc p) (fc (p / 4)) (fc (p / 16))

@[expose] def colsS1 : List (List ℕ) := [
    [1, 2, 4, 8, 16, 32, 64, 128, 256], [1, 11, 4, 8, 17, 32, 64, 160, 320],
    [1, 19, 4, 9, 16, 32, 64, 192, 352], [1, 27, 4, 9, 17, 32, 64, 224, 288],
    [1, 2, 37, 8, 16, 32, 65, 136, 280], [1, 11, 37, 8, 17, 32, 65, 168, 345],
    [1, 19, 37, 9, 16, 32, 65, 201, 377], [1, 27, 37, 9, 17, 32, 65, 233, 312],
    [1, 2, 69, 8, 16, 33, 64, 144, 264], [1, 11, 69, 8, 17, 33, 64, 177, 328],
    [1, 19, 69, 9, 16, 33, 64, 208, 361], [1, 27, 69, 9, 17, 33, 64, 241, 297],
    [1, 2, 101, 8, 16, 33, 65, 152, 272], [1, 11, 101, 8, 17, 33, 65, 185, 337],
    [1, 19, 101, 9, 16, 33, 65, 217, 368], [1, 27, 101, 9, 17, 33, 65, 248, 305],
    [1, 2, 134, 8, 16, 40, 80, 128, 258], [1, 11, 134, 8, 17, 40, 80, 168, 338],
    [1, 19, 134, 9, 16, 40, 80, 208, 378], [1, 27, 134, 9, 17, 40, 80, 248, 298],
    [1, 2, 175, 8, 16, 40, 81, 136, 282], [1, 11, 175, 8, 17, 40, 81, 160, 331],
    [1, 19, 175, 9, 16, 40, 81, 217, 355], [1, 27, 175, 9, 17, 40, 81, 241, 306],
    [1, 2, 215, 8, 16, 41, 80, 144, 266], [1, 11, 215, 8, 17, 41, 80, 185, 346],
    [1, 19, 215, 9, 16, 41, 80, 192, 371], [1, 27, 215, 9, 17, 41, 80, 233, 291],
    [1, 2, 255, 8, 16, 41, 81, 152, 274], [1, 11, 255, 8, 17, 41, 81, 177, 323],
    [1, 19, 255, 9, 16, 41, 81, 201, 362], [1, 27, 255, 9, 17, 41, 81, 224, 315],
    [1, 2, 262, 8, 16, 56, 72, 130, 256], [1, 11, 262, 8, 17, 56, 72, 186, 328],
    [1, 19, 262, 9, 16, 56, 72, 202, 368], [1, 27, 262, 9, 17, 56, 72, 242, 312],
    [1, 2, 319, 8, 16, 56, 73, 138, 280], [1, 11, 319, 8, 17, 56, 73, 178, 337],
    [1, 19, 319, 9, 16, 56, 73, 195, 361], [1, 27, 319, 9, 17, 56, 73, 251, 288],
    [1, 2, 335, 8, 16, 57, 72, 146, 264], [1, 11, 335, 8, 17, 57, 72, 171, 320],
    [1, 19, 335, 9, 16, 57, 72, 218, 377], [1, 27, 335, 9, 17, 57, 72, 227, 305],
    [1, 2, 375, 8, 16, 57, 73, 154, 272], [1, 11, 375, 8, 17, 57, 73, 163, 345],
    [1, 19, 375, 9, 16, 57, 73, 211, 352], [1, 27, 375, 9, 17, 57, 73, 234, 297],
    [1, 2, 390, 8, 16, 48, 88, 130, 258], [1, 11, 390, 8, 17, 48, 88, 178, 346],
    [1, 19, 390, 9, 16, 48, 88, 218, 362], [1, 27, 390, 9, 17, 48, 88, 234, 306],
    [1, 2, 439, 8, 16, 48, 89, 138, 282], [1, 11, 439, 8, 17, 48, 89, 186, 323],
    [1, 19, 439, 9, 16, 48, 89, 211, 371], [1, 27, 439, 9, 17, 48, 89, 227, 298],
    [1, 2, 479, 8, 16, 49, 88, 146, 266], [1, 11, 479, 8, 17, 49, 88, 163, 338],
    [1, 19, 479, 9, 16, 49, 88, 202, 355], [1, 27, 479, 9, 17, 49, 88, 251, 315],
    [1, 2, 495, 8, 16, 49, 89, 154, 274], [1, 11, 495, 8, 17, 49, 89, 171, 331],
    [1, 19, 495, 9, 16, 49, 89, 195, 378], [1, 27, 495, 9, 17, 49, 89, 242, 291]]

theorem cols_s : ∀ p < 64, cols (sM p) = colsS1.getD p [] := by
  decide +kernel

theorem s_nodup : ((List.range 64).map fun p => colsS1.getD p []).Nodup := by
  decide +kernel

@[expose] def sWords : List (List ℕ) := [
    [], [1, 1, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 1, 1, 1, 1, 0, 0], [1, 1, 1, 0, 0, 1, 1],
    [1, 1, 1, 0, 0, 1, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0, 1, 1], [1, 1, 0, 0, 1, 1, 1],
    [1, 1, 1, 1, 0, 0, 1], [1, 0, 0, 1, 1, 1, 1], [1, 1, 1, 0, 0, 1, 1, 0, 0], [0, 0],
    [1, 0, 0, 1, 1, 0, 0, 1, 1], [1, 1, 0, 0, 1, 1, 1, 0, 0], [1, 1, 1, 1, 0, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 0, 1, 1, 1], [1, 0, 0, 1, 1, 1, 0, 0, 1], [1, 0, 1, 0, 0, 1, 1, 1],
    [1, 0, 1, 1, 1, 0, 0, 1], [1, 0, 1, 1, 0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 1, 1, 1, 0, 0, 1],
    [0, 0, 1, 0, 1, 1, 1, 1], [1, 0, 1, 1, 0, 0, 1, 1], [1, 0, 1, 1, 1, 1],
    [1, 0, 1, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 0, 1, 0, 0, 1, 1, 1],
    [1, 1, 1, 0, 1, 1, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 1, 1, 0, 0],
    [1, 0, 1, 1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 1, 1, 0, 0], [1, 0, 0, 0, 1, 1, 0, 0, 1, 1],
    [1, 1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 1, 0, 0, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0], [1, 0, 1, 0, 1, 1, 1, 1, 0],
    [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1], [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0],
    [1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0], [0, 0, 0, 1, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1], [1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0],
    [0, 1, 1, 1, 1, 0, 1, 0, 1, 1], [0, 1, 1, 0, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0],
    [1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 0, 1, 1, 0, 1],
    [0, 1, 0, 0, 0, 1, 0, 0, 1, 1], [1, 1, 0, 1, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0, 0, 1],
    [0, 1, 1, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 1], [0, 1, 0, 1, 1, 1],
    [0, 1, 0, 1, 0, 0, 1, 1], [0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 1, 0, 0, 1, 0, 0],
    [1, 1, 1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0], [0, 0, 0, 1, 0, 1, 1, 1],
    [0, 1, 0, 1, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 1, 0, 0, 1, 1, 0],
    [0, 1, 1, 1, 0, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 1, 0, 0]]

@[expose] def sWord (p : ℕ) : List ℕ := sWords.getD p []

theorem sWord_ok : ∀ p < 64, cols (wM [xM, yM] (sWord p)) = colsS1.getD p [] := by
  decide +kernel

theorem s_conj : ∀ p < 64, 16 ≤ p → cols (yMi * sM p * yM) ∉ colsS1 := by
  decide +kernel

end CFSG.Quasithin.H.L34Z
