module

public import CFSG.LocalAnalysis.StandardType.GGF4WeylData

public section

namespace CFSG.StandardType.F4Model

@[expose] def ord2b (x y : M4) : Bool := pw2 (x.mul y) == M4.one && x.mul y != M4.one

@[expose] def ord3b (x y : M4) : Bool := pw3 (x.mul y) == M4.one && x.mul y != M4.one

@[expose] def ord4b (x y : M4) : Bool := pw4 (x.mul y) == M4.one && pw2 (x.mul y) != M4.one

@[expose] def quadF (a b c d : M4) : Fin 4 → M4 :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

@[expose] def evalG (x : Fin 4 → M4) (l : List (Fin 4)) : M4 :=
  l.foldr (fun i m => (x i).mul m) M4.one

@[expose] def famOk (m : Fin 4 → M4) : Bool :=
  decide (∀ j k : Fin 4, (m j).mul (m k) = (m k).mul (m j)) &&
    decide (∀ j k : Fin 4, j ≠ k → m j ≠ m k)

theorem famOk_iff (m : Fin 4 → M4) : famOk m = true ↔
    ((∀ j k : Fin 4, (m j).mul (m k) = (m k).mul (m j)) ∧
      (∀ j k : Fin 4, j ≠ k → m j ≠ m k)) := by
  simp [famOk]

theorem ord2b_iff (x y : M4) :
    ord2b x y = true ↔ (pw2 (x.mul y) = M4.one ∧ x.mul y ≠ M4.one) := by
  simp [ord2b]

theorem ord3b_iff (x y : M4) :
    ord3b x y = true ↔ (pw3 (x.mul y) = M4.one ∧ x.mul y ≠ M4.one) := by
  simp [ord3b]

theorem ord4b_iff (x y : M4) :
    ord4b x y = true ↔ (pw4 (x.mul y) = M4.one ∧ pw2 (x.mul y) ≠ M4.one) := by
  simp [ord4b]

@[expose] def wB0 : List (Fin 4) := [0, 1, 2, 3, 2, 1, 0]
@[expose] def wB1 : List (Fin 4) := [1, 2, 3, 2, 1]
@[expose] def wB2 : List (Fin 4) := [2, 3, 2]
@[expose] def wB3 : List (Fin 4) := [3]

@[expose] def wD0 : List (Fin 4) := [0]
@[expose] def wD1 : List (Fin 4) := [2]
@[expose] def wD2 : List (Fin 4) := [3]
@[expose] def wD3 : List (Fin 4) := [1, 0, 2, 3, 1, 3, 2, 0, 1]

@[expose] def wordsB (j : Fin 4) : List (Fin 4) :=
  if j.val = 0 then wB0 else if j.val = 1 then wB1 else if j.val = 2 then wB2 else wB3

@[expose] def wordsD (j : Fin 4) : List (Fin 4) :=
  if j.val = 0 then wD0 else if j.val = 1 then wD1 else if j.val = 2 then wD2 else wD3

private def ordData : List (List Nat) :=
  [[1, 4, 4, 3, 4, 3, 3, 3, 4, 3, 3, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3],
   [4, 1, 3, 4, 3, 4, 4, 2, 3, 4, 2, 3, 2, 3, 2, 3, 2, 2, 4, 2, 3, 3, 2, 2],
   [4, 3, 1, 4, 3, 4, 2, 4, 3, 2, 4, 2, 3, 3, 3, 2, 2, 4, 2, 3, 2, 3, 2, 2],
   [3, 4, 4, 1, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 2, 3],
   [4, 3, 3, 4, 1, 2, 4, 4, 2, 2, 2, 3, 3, 2, 3, 3, 4, 2, 2, 3, 3, 2, 4, 2],
   [3, 4, 4, 3, 2, 1, 2, 2, 4, 3, 3, 2, 2, 2, 4, 4, 3, 3, 3, 2, 2, 4, 3, 2],
   [3, 4, 2, 3, 4, 2, 1, 2, 2, 3, 3, 4, 2, 4, 4, 2, 3, 3, 3, 2, 4, 2, 3, 2],
   [3, 2, 4, 3, 4, 2, 2, 1, 2, 3, 3, 2, 4, 4, 2, 4, 3, 3, 3, 4, 2, 2, 3, 2],
   [4, 3, 3, 2, 2, 4, 2, 2, 1, 4, 4, 3, 3, 2, 3, 3, 4, 2, 2, 3, 3, 2, 2, 4],
   [3, 4, 2, 2, 2, 3, 3, 3, 4, 1, 2, 4, 2, 4, 2, 4, 3, 3, 3, 4, 2, 2, 2, 3],
   [3, 2, 4, 2, 2, 3, 3, 3, 4, 2, 1, 2, 4, 4, 4, 2, 3, 3, 3, 2, 4, 2, 2, 3],
   [4, 3, 2, 2, 3, 2, 4, 2, 3, 4, 2, 1, 3, 3, 3, 2, 2, 4, 2, 3, 2, 3, 4, 4],
   [4, 2, 3, 2, 3, 2, 2, 4, 3, 2, 4, 3, 1, 3, 2, 3, 2, 2, 4, 2, 3, 3, 4, 4],
   [2, 3, 3, 2, 2, 2, 4, 4, 2, 4, 4, 3, 3, 1, 3, 3, 2, 4, 4, 3, 3, 2, 2, 2],
   [2, 2, 3, 2, 3, 4, 4, 2, 3, 2, 4, 3, 2, 3, 1, 3, 4, 4, 2, 2, 3, 3, 4, 2],
   [2, 3, 2, 2, 3, 4, 2, 4, 3, 4, 2, 2, 3, 3, 3, 1, 4, 2, 4, 3, 2, 3, 4, 2],
   [2, 2, 2, 3, 4, 3, 3, 3, 4, 3, 3, 2, 2, 2, 4, 4, 1, 2, 2, 4, 4, 2, 3, 3],
   [2, 2, 4, 3, 2, 3, 3, 3, 2, 3, 3, 4, 2, 4, 4, 2, 2, 1, 2, 4, 2, 4, 3, 3],
   [2, 4, 2, 3, 2, 3, 3, 3, 2, 3, 3, 2, 4, 4, 2, 4, 2, 2, 1, 2, 4, 4, 3, 3],
   [2, 2, 3, 4, 3, 2, 2, 4, 3, 4, 2, 3, 2, 3, 2, 3, 4, 4, 2, 1, 3, 3, 2, 4],
   [2, 3, 2, 4, 3, 2, 4, 2, 3, 2, 4, 2, 3, 3, 3, 2, 4, 2, 4, 3, 1, 3, 2, 4],
   [2, 3, 3, 4, 2, 4, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 4, 4, 3, 3, 1, 4, 4],
   [3, 2, 2, 2, 4, 3, 3, 3, 2, 2, 2, 4, 4, 2, 4, 4, 3, 3, 3, 2, 2, 4, 1, 3],
   [3, 2, 2, 3, 2, 2, 2, 2, 4, 3, 3, 4, 4, 2, 2, 2, 3, 3, 3, 4, 4, 4, 3, 1]]

private def cjData : List (List Nat) :=
  [[0, 12, 11, 23, 8, 22, 10, 9, 4, 7, 6, 2, 1, 13, 14, 15, 16, 17, 18, 19, 20, 21, 5, 3],
   [18, 1, 13, 9, 15, 6, 5, 7, 20, 3, 10, 21, 12, 2, 14, 4, 16, 17, 0, 19, 8, 11, 22, 23],
   [17, 13, 2, 10, 14, 7, 6, 5, 19, 9, 3, 11, 21, 1, 4, 15, 16, 0, 18, 8, 20, 12, 22, 23],
   [23, 19, 20, 3, 21, 16, 17, 18, 8, 9, 10, 11, 12, 13, 14, 15, 5, 6, 7, 1, 2, 4, 22, 0],
   [16, 15, 14, 22, 4, 5, 7, 6, 8, 9, 10, 19, 20, 13, 2, 1, 0, 17, 18, 11, 12, 21, 3, 23],
   [22, 14, 15, 16, 4, 5, 6, 7, 21, 17, 18, 11, 12, 13, 1, 2, 3, 9, 10, 19, 20, 8, 0, 23],
   [10, 14, 2, 17, 13, 5, 6, 7, 8, 16, 0, 20, 12, 4, 1, 15, 9, 3, 22, 19, 11, 21, 18, 23],
   [9, 1, 15, 18, 13, 5, 6, 7, 8, 0, 16, 11, 19, 4, 14, 2, 10, 22, 3, 12, 20, 21, 17, 23],
   [16, 20, 19, 3, 4, 23, 6, 7, 8, 10, 9, 14, 15, 13, 11, 12, 0, 17, 18, 2, 1, 21, 22, 5],
   [7, 19, 2, 3, 4, 17, 16, 0, 13, 9, 10, 15, 12, 8, 14, 11, 6, 5, 23, 1, 20, 21, 22, 18],
   [6, 1, 20, 3, 4, 18, 0, 16, 13, 9, 10, 11, 14, 8, 12, 15, 7, 23, 5, 19, 2, 21, 22, 17],
   [17, 21, 2, 3, 19, 5, 23, 7, 14, 22, 10, 11, 13, 12, 8, 15, 16, 0, 18, 4, 20, 1, 9, 6],
   [18, 1, 21, 3, 20, 5, 6, 23, 15, 9, 22, 13, 12, 11, 14, 8, 16, 17, 0, 19, 4, 2, 10, 7],
   [0, 2, 1, 3, 4, 5, 7, 6, 8, 10, 9, 12, 11, 13, 15, 14, 16, 18, 17, 20, 19, 21, 22, 23],
   [0, 1, 4, 3, 2, 6, 5, 7, 11, 9, 22, 8, 12, 15, 14, 13, 17, 16, 18, 19, 21, 20, 10, 23],
   [0, 4, 2, 3, 1, 7, 6, 5, 12, 22, 10, 11, 8, 14, 13, 15, 18, 17, 16, 21, 20, 19, 9, 23],
   [0, 1, 2, 5, 8, 3, 9, 10, 4, 6, 7, 11, 12, 13, 19, 20, 16, 17, 18, 14, 15, 21, 23, 22],
   [0, 1, 11, 6, 4, 9, 3, 22, 8, 5, 23, 2, 12, 21, 19, 15, 16, 17, 18, 14, 20, 13, 7, 10],
   [0, 12, 2, 7, 4, 10, 22, 3, 8, 23, 5, 11, 1, 21, 14, 20, 16, 17, 18, 19, 15, 13, 6, 9],
   [0, 1, 8, 9, 11, 5, 6, 23, 2, 3, 10, 4, 12, 20, 14, 21, 17, 16, 18, 19, 13, 15, 22, 7],
   [0, 8, 2, 10, 12, 5, 23, 7, 1, 9, 3, 11, 4, 19, 21, 15, 18, 17, 16, 13, 20, 14, 22, 6],
   [0, 11, 12, 22, 4, 23, 6, 7, 8, 9, 10, 1, 2, 13, 20, 19, 16, 18, 17, 15, 14, 21, 3, 5],
   [5, 1, 2, 3, 21, 0, 18, 17, 8, 9, 10, 15, 14, 13, 12, 11, 23, 7, 6, 19, 20, 4, 22, 16],
   [3, 1, 2, 0, 4, 5, 6, 7, 21, 18, 17, 20, 19, 13, 14, 15, 22, 10, 9, 12, 11, 8, 16, 23]]

private def ordT (a b : Nat) : Nat := (ordData.getD a []).getD b 0

private def cjT (a b : Nat) : Nat := (cjData.getD a []).getD b 0

private theorem ordT_spec : ∀ a, a < 24 → ∀ b, b < 24 →
    ord2b (Rm a) (Rm b) = (ordT a b == 2) ∧ ord3b (Rm a) (Rm b) = (ordT a b == 3) ∧
      ord4b (Rm a) (Rm b) = (ordT a b == 4) := by
  decide +kernel

private theorem cjT_spec : ∀ a, a < 24 → ∀ b, b < 24 →
    cjT a b < 24 ∧ (Rm a).mul ((Rm b).mul (Rm a)) = Rm (cjT a b) := by
  decide +kernel

private theorem M4_mul_assoc (x y z : M4) : (x.mul y).mul z = x.mul (y.mul z) := by
  cases x; cases y; cases z
  simp only [M4.mul, M4.mk.injEq, Int.add_mul, Int.mul_add, Int.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem M4_mul_one (x : M4) : x.mul M4.one = x := by
  cases x; simp [M4.mul, M4.one]

private theorem M4_one_mul (x : M4) : M4.one.mul x = x := by
  cases x; simp [M4.mul, M4.one]

private theorem comm_ne_of_ordT {a b : Nat} (ha : a < 24) (hb : b < 24) (h : ordT a b = 2) :
    (Rm a).mul (Rm b) = (Rm b).mul (Rm a) ∧ Rm a ≠ Rm b := by
  have h2 : ord2b (Rm a) (Rm b) = true := by rw [(ordT_spec a ha b hb).1, h]; rfl
  obtain ⟨hsq, hne⟩ := (ord2b_iff _ _).1 h2
  refine ⟨?_, fun e => hne (by rw [e]; exact Rm_sq b hb)⟩
  calc (Rm a).mul (Rm b) = (Rm b).mul ((Rm b).mul ((Rm a).mul (Rm b))) := by
        rw [← M4_mul_assoc (Rm b) (Rm b), Rm_sq b hb, M4_one_mul]
    _ = (Rm b).mul ((Rm a).mul (((Rm a).mul (Rm b)).mul ((Rm a).mul (Rm b)))) := by
        rw [M4_mul_assoc (Rm a) (Rm b), ← M4_mul_assoc (Rm a) (Rm a), Rm_sq a ha, M4_one_mul]
    _ = (Rm b).mul (Rm a) := by
        rw [show ((Rm a).mul (Rm b)).mul ((Rm a).mul (Rm b)) = M4.one from hsq, M4_mul_one]

private theorem Rm_conj_mul {a b : Nat} (ha : a < 24) (hb : b < 24) (y : M4) :
    (Rm a).mul ((Rm b).mul ((Rm a).mul y)) = (Rm (cjT a b)).mul y := by
  have e := congrArg (fun z => z.mul y) (cjT_spec a ha b hb).2
  simpa only [M4_mul_assoc] using e

private def okQ (a b c d : Nat) : Bool :=
  ordT a b == 2 && ordT a c == 2 && ordT a d == 2 && ordT b c == 2 && ordT b d == 2 &&
    ordT c d == 2

private theorem famOk_okQ {a b c d : Nat} (ha : a < 24) (hb : b < 24) (hc : c < 24)
    (hd : d < 24) (h : okQ a b c d = true) :
    famOk (quadF (Rm a) (Rm b) (Rm c) (Rm d)) = true := by
  simp only [okQ, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hab, hac⟩, had⟩, hbc⟩, hbd⟩, hcd⟩ := h
  obtain ⟨cab, nab⟩ := comm_ne_of_ordT ha hb hab
  obtain ⟨cac, nac⟩ := comm_ne_of_ordT ha hc hac
  obtain ⟨cad, nad⟩ := comm_ne_of_ordT ha hd had
  obtain ⟨cbc, nbc⟩ := comm_ne_of_ordT hb hc hbc
  obtain ⟨cbd, nbd⟩ := comm_ne_of_ordT hb hd hbd
  obtain ⟨ccd, ncd⟩ := comm_ne_of_ordT hc hd hcd
  rw [famOk_iff]
  refine ⟨fun j k => ?_, fun j k => ?_⟩ <;>
    rcases j with ⟨_ | _ | _ | _ | j, hj⟩ <;> rcases k with ⟨_ | _ | _ | _ | k, hk⟩ <;>
    first
    | exact absurd hj (by omega)
    | exact absurd hk (by omega)
    | simp [quadF, cab, cac, cad, cbc, cbd, ccd, nab, nac, nad, nbc, nbd, ncd, nab.symm,
        nac.symm, nad.symm, nbc.symm, nbd.symm, ncd.symm]

private theorem quadF_0 (a b c d : M4) : quadF a b c d 0 = a := rfl
private theorem quadF_1 (a b c d : M4) : quadF a b c d 1 = b := rfl
private theorem quadF_2 (a b c d : M4) : quadF a b c d 2 = c := rfl
private theorem quadF_3 (a b c d : M4) : quadF a b c d 3 = d := rfl

private theorem evalG_wordsB {x0 x1 x2 x3 : Nat} (h0 : x0 < 24) (h1 : x1 < 24) (h2 : x2 < 24)
    (h3 : x3 < 24) :
    (fun j => evalG (quadF (Rm x0) (Rm x1) (Rm x2) (Rm x3)) (wordsB j)) =
      quadF (Rm (cjT x0 (cjT x1 (cjT x2 x3)))) (Rm (cjT x1 (cjT x2 x3))) (Rm (cjT x2 x3))
        (Rm x3) := by
  have c23 := (cjT_spec x2 h2 x3 h3).1
  have c123 := (cjT_spec x1 h1 _ c23).1
  funext j
  rcases j with ⟨_ | _ | _ | _ | j, hj⟩
  · show evalG _ wB0 = Rm (cjT x0 (cjT x1 (cjT x2 x3)))
    simp only [evalG, wB0, List.foldr_cons, List.foldr_nil, quadF_0, quadF_1, quadF_2, quadF_3]
    rw [Rm_conj_mul h2 h3, Rm_conj_mul h1 c23, Rm_conj_mul h0 c123, M4_mul_one]
  · show evalG _ wB1 = Rm (cjT x1 (cjT x2 x3))
    simp only [evalG, wB1, List.foldr_cons, List.foldr_nil, quadF_1, quadF_2, quadF_3]
    rw [Rm_conj_mul h2 h3, Rm_conj_mul h1 c23, M4_mul_one]
  · show evalG _ wB2 = Rm (cjT x2 x3)
    simp only [evalG, wB2, List.foldr_cons, List.foldr_nil, quadF_2, quadF_3]
    rw [Rm_conj_mul h2 h3, M4_mul_one]
  · show evalG _ wB3 = Rm x3
    simp only [evalG, wB3, List.foldr_cons, List.foldr_nil, quadF_3]
    rw [M4_mul_one]
  · exact absurd hj (by omega)

private theorem evalG_wordsD {x0 x1 x2 x3 : Nat} (h0 : x0 < 24) (h1 : x1 < 24) (h2 : x2 < 24)
    (h3 : x3 < 24) :
    (fun j => evalG (quadF (Rm x0) (Rm x1) (Rm x2) (Rm x3)) (wordsD j)) =
      quadF (Rm x0) (Rm x2) (Rm x3) (Rm (cjT x1 (cjT x0 (cjT x2 (cjT x3 x1))))) := by
  have c31 := (cjT_spec x3 h3 x1 h1).1
  have c231 := (cjT_spec x2 h2 _ c31).1
  have c0231 := (cjT_spec x0 h0 _ c231).1
  funext j
  rcases j with ⟨_ | _ | _ | _ | j, hj⟩
  · show evalG _ wD0 = Rm x0
    simp only [evalG, wD0, List.foldr_cons, List.foldr_nil, quadF_0]
    rw [M4_mul_one]
  · show evalG _ wD1 = Rm x2
    simp only [evalG, wD1, List.foldr_cons, List.foldr_nil, quadF_2]
    rw [M4_mul_one]
  · show evalG _ wD2 = Rm x3
    simp only [evalG, wD2, List.foldr_cons, List.foldr_nil, quadF_3]
    rw [M4_mul_one]
  · show evalG _ wD3 = Rm (cjT x1 (cjT x0 (cjT x2 (cjT x3 x1))))
    simp only [evalG, wD3, List.foldr_cons, List.foldr_nil, quadF_0, quadF_1, quadF_2, quadF_3]
    rw [Rm_conj_mul h3 h1, Rm_conj_mul h2 c31, Rm_conj_mul h0 c231, Rm_conj_mul h1 c0231,
      M4_mul_one]
  · exact absurd hj (by omega)

@[expose] def chkB3 (x0 x1 x2 : Nat) : Bool :=
  (List.range 24).all fun x3 =>
    if ord2b (Rm x0) (Rm x3) && ord2b (Rm x1) (Rm x3) && ord4b (Rm x2) (Rm x3) then
      famOk (fun j => evalG (quadF (Rm x0) (Rm x1) (Rm x2) (Rm x3)) (wordsB j))
    else true

@[expose] def chkB2 (x0 x1 : Nat) : Bool :=
  (List.range 24).all fun x2 =>
    if ord2b (Rm x0) (Rm x2) && ord3b (Rm x1) (Rm x2) then chkB3 x0 x1 x2 else true

@[expose] def chkB1 (x0 : Nat) : Bool :=
  (List.range 24).all fun x1 => if ord3b (Rm x0) (Rm x1) then chkB2 x0 x1 else true

private def fB3 (x0 x1 x2 : Nat) : Bool :=
  (List.range 24).all fun x3 =>
    if ordT x0 x3 == 2 && ordT x1 x3 == 2 && ordT x2 x3 == 4 then
      okQ (cjT x0 (cjT x1 (cjT x2 x3))) (cjT x1 (cjT x2 x3)) (cjT x2 x3) x3
    else true

private def fB2 (x0 x1 : Nat) : Bool :=
  (List.range 24).all fun x2 =>
    if ordT x0 x2 == 2 && ordT x1 x2 == 3 then fB3 x0 x1 x2 else true

private def fB1 (x0 : Nat) : Bool :=
  (List.range 24).all fun x1 => if ordT x0 x1 == 3 then fB2 x0 x1 else true

private theorem fB1_all : ∀ x0, x0 < 24 → fB1 x0 = true := by decide +kernel

private theorem chkB3_of_fB3 {x0 x1 x2 : Nat} (h0 : x0 < 24) (h1 : x1 < 24) (h2 : x2 < 24)
    (h : fB3 x0 x1 x2 = true) : chkB3 x0 x1 x2 = true := by
  unfold chkB3
  refine List.all_eq_true.2 fun x3 hx3 => ?_
  have h3 := List.mem_range.1 hx3
  have hq := List.all_eq_true.1 h x3 hx3
  rw [(ordT_spec x0 h0 x3 h3).1, (ordT_spec x1 h1 x3 h3).1, (ordT_spec x2 h2 x3 h3).2.2]
  split
  · next hc =>
    rw [if_pos hc] at hq
    rw [evalG_wordsB h0 h1 h2 h3]
    have c23 := (cjT_spec x2 h2 x3 h3).1
    have c123 := (cjT_spec x1 h1 _ c23).1
    exact famOk_okQ (cjT_spec x0 h0 _ c123).1 c123 c23 h3 hq
  · rfl

private theorem chkB2_of_fB2 {x0 x1 : Nat} (h0 : x0 < 24) (h1 : x1 < 24)
    (h : fB2 x0 x1 = true) : chkB2 x0 x1 = true := by
  unfold chkB2
  refine List.all_eq_true.2 fun x2 hx2 => ?_
  have h2 := List.mem_range.1 hx2
  have hq := List.all_eq_true.1 h x2 hx2
  rw [(ordT_spec x0 h0 x2 h2).1, (ordT_spec x1 h1 x2 h2).2.1]
  split
  · next hc =>
    rw [if_pos hc] at hq
    exact chkB3_of_fB3 h0 h1 h2 hq
  · rfl

private theorem chkB1_of_fB1 {x0 : Nat} (h0 : x0 < 24) (h : fB1 x0 = true) :
    chkB1 x0 = true := by
  unfold chkB1
  refine List.all_eq_true.2 fun x1 hx1 => ?_
  have h1 := List.mem_range.1 hx1
  have hq := List.all_eq_true.1 h x1 hx1
  rw [(ordT_spec x0 h0 x1 h1).2.1]
  split
  · next hc =>
    rw [if_pos hc] at hq
    exact chkB2_of_fB2 h0 h1 hq
  · rfl

theorem chkB1_all (x0 : Nat) (hx0 : x0 < 24) : chkB1 x0 = true :=
  chkB1_of_fB1 hx0 (fB1_all x0 hx0)

theorem chkB3_spec {x0 x1 x2 x3 : Nat} (h : chkB3 x0 x1 x2 = true) (hx3 : x3 < 24)
    (h23 : ord4b (Rm x2) (Rm x3) = true) (h03 : ord2b (Rm x0) (Rm x3) = true)
    (h13 : ord2b (Rm x1) (Rm x3) = true) :
    famOk (fun j => evalG (quadF (Rm x0) (Rm x1) (Rm x2) (Rm x3)) (wordsB j)) = true := by
  unfold chkB3 at h
  have h' := List.all_eq_true.1 h x3 (List.mem_range.2 hx3)
  simpa [h23, h03, h13] using h'

theorem chkB2_spec {x0 x1 x2 : Nat} (h : chkB2 x0 x1 = true) (hx2 : x2 < 24)
    (h12 : ord3b (Rm x1) (Rm x2) = true) (h02 : ord2b (Rm x0) (Rm x2) = true) :
    chkB3 x0 x1 x2 = true := by
  unfold chkB2 at h
  have h' := List.all_eq_true.1 h x2 (List.mem_range.2 hx2)
  simpa [h12, h02] using h'

theorem chkB1_spec {x0 x1 : Nat} (h : chkB1 x0 = true) (hx1 : x1 < 24)
    (h01 : ord3b (Rm x0) (Rm x1) = true) : chkB2 x0 x1 = true := by
  unfold chkB1 at h
  have h' := List.all_eq_true.1 h x1 (List.mem_range.2 hx1)
  simpa [h01] using h'

theorem quadB :
    ∀ x0, x0 < 24 → ∀ x1, x1 < 24 → ord3b (Rm x0) (Rm x1) = true →
      ∀ x2, x2 < 24 → ord3b (Rm x1) (Rm x2) = true → ord2b (Rm x0) (Rm x2) = true →
        ∀ x3, x3 < 24 → ord4b (Rm x2) (Rm x3) = true → ord2b (Rm x0) (Rm x3) = true →
          ord2b (Rm x1) (Rm x3) = true →
            famOk (fun j => evalG (quadF (Rm x0) (Rm x1) (Rm x2) (Rm x3)) (wordsB j)) = true := by
  intro x0 hx0 x1 hx1 h01 x2 hx2 h12 h02 x3 hx3 h23 h03 h13
  exact chkB3_spec (chkB2_spec (chkB1_spec (chkB1_all x0 hx0) hx1 h01) hx2 h12 h02) hx3 h23 h03 h13

@[expose] def chkD3 (x0 x1 x2 : Nat) : Bool :=
  (List.range 24).all fun x3 =>
    if ord2b (Rm x0) (Rm x3) && ord2b (Rm x2) (Rm x3) && ord3b (Rm x1) (Rm x3) then
      famOk (fun j => evalG (quadF (Rm x0) (Rm x1) (Rm x2) (Rm x3)) (wordsD j))
    else true

@[expose] def chkD2 (x0 x1 : Nat) : Bool :=
  (List.range 24).all fun x2 =>
    if ord2b (Rm x0) (Rm x2) && ord3b (Rm x1) (Rm x2) then chkD3 x0 x1 x2 else true

@[expose] def chkD1 (x0 : Nat) : Bool :=
  (List.range 24).all fun x1 => if ord3b (Rm x0) (Rm x1) then chkD2 x0 x1 else true

private def fD3 (x0 x1 x2 : Nat) : Bool :=
  (List.range 24).all fun x3 =>
    if ordT x0 x3 == 2 && ordT x2 x3 == 2 && ordT x1 x3 == 3 then
      okQ x0 x2 x3 (cjT x1 (cjT x0 (cjT x2 (cjT x3 x1))))
    else true

private def fD2 (x0 x1 : Nat) : Bool :=
  (List.range 24).all fun x2 =>
    if ordT x0 x2 == 2 && ordT x1 x2 == 3 then fD3 x0 x1 x2 else true

private def fD1 (x0 : Nat) : Bool :=
  (List.range 24).all fun x1 => if ordT x0 x1 == 3 then fD2 x0 x1 else true

private theorem fD1_all : ∀ x0, x0 < 24 → fD1 x0 = true := by decide +kernel

private theorem chkD3_of_fD3 {x0 x1 x2 : Nat} (h0 : x0 < 24) (h1 : x1 < 24) (h2 : x2 < 24)
    (h : fD3 x0 x1 x2 = true) : chkD3 x0 x1 x2 = true := by
  unfold chkD3
  refine List.all_eq_true.2 fun x3 hx3 => ?_
  have h3 := List.mem_range.1 hx3
  have hq := List.all_eq_true.1 h x3 hx3
  rw [(ordT_spec x0 h0 x3 h3).1, (ordT_spec x2 h2 x3 h3).1, (ordT_spec x1 h1 x3 h3).2.1]
  split
  · next hc =>
    rw [if_pos hc] at hq
    rw [evalG_wordsD h0 h1 h2 h3]
    have c31 := (cjT_spec x3 h3 x1 h1).1
    have c231 := (cjT_spec x2 h2 _ c31).1
    have c0231 := (cjT_spec x0 h0 _ c231).1
    exact famOk_okQ h0 h2 h3 (cjT_spec x1 h1 _ c0231).1 hq
  · rfl

private theorem chkD2_of_fD2 {x0 x1 : Nat} (h0 : x0 < 24) (h1 : x1 < 24)
    (h : fD2 x0 x1 = true) : chkD2 x0 x1 = true := by
  unfold chkD2
  refine List.all_eq_true.2 fun x2 hx2 => ?_
  have h2 := List.mem_range.1 hx2
  have hq := List.all_eq_true.1 h x2 hx2
  rw [(ordT_spec x0 h0 x2 h2).1, (ordT_spec x1 h1 x2 h2).2.1]
  split
  · next hc =>
    rw [if_pos hc] at hq
    exact chkD3_of_fD3 h0 h1 h2 hq
  · rfl

private theorem chkD1_of_fD1 {x0 : Nat} (h0 : x0 < 24) (h : fD1 x0 = true) :
    chkD1 x0 = true := by
  unfold chkD1
  refine List.all_eq_true.2 fun x1 hx1 => ?_
  have h1 := List.mem_range.1 hx1
  have hq := List.all_eq_true.1 h x1 hx1
  rw [(ordT_spec x0 h0 x1 h1).2.1]
  split
  · next hc =>
    rw [if_pos hc] at hq
    exact chkD2_of_fD2 h0 h1 hq
  · rfl

theorem chkD1_all (x0 : Nat) (hx0 : x0 < 24) : chkD1 x0 = true :=
  chkD1_of_fD1 hx0 (fD1_all x0 hx0)

theorem chkD3_spec {x0 x1 x2 x3 : Nat} (h : chkD3 x0 x1 x2 = true) (hx3 : x3 < 24)
    (h13 : ord3b (Rm x1) (Rm x3) = true) (h03 : ord2b (Rm x0) (Rm x3) = true)
    (h23 : ord2b (Rm x2) (Rm x3) = true) :
    famOk (fun j => evalG (quadF (Rm x0) (Rm x1) (Rm x2) (Rm x3)) (wordsD j)) = true := by
  unfold chkD3 at h
  have h' := List.all_eq_true.1 h x3 (List.mem_range.2 hx3)
  simpa [h13, h03, h23] using h'

theorem chkD2_spec {x0 x1 x2 : Nat} (h : chkD2 x0 x1 = true) (hx2 : x2 < 24)
    (h12 : ord3b (Rm x1) (Rm x2) = true) (h02 : ord2b (Rm x0) (Rm x2) = true) :
    chkD3 x0 x1 x2 = true := by
  unfold chkD2 at h
  have h' := List.all_eq_true.1 h x2 (List.mem_range.2 hx2)
  simpa [h12, h02] using h'

theorem chkD1_spec {x0 x1 : Nat} (h : chkD1 x0 = true) (hx1 : x1 < 24)
    (h01 : ord3b (Rm x0) (Rm x1) = true) : chkD2 x0 x1 = true := by
  unfold chkD1 at h
  have h' := List.all_eq_true.1 h x1 (List.mem_range.2 hx1)
  simpa [h01] using h'

theorem quadD :
    ∀ x0, x0 < 24 → ∀ x1, x1 < 24 → ord3b (Rm x0) (Rm x1) = true →
      ∀ x2, x2 < 24 → ord3b (Rm x1) (Rm x2) = true → ord2b (Rm x0) (Rm x2) = true →
        ∀ x3, x3 < 24 → ord3b (Rm x1) (Rm x3) = true → ord2b (Rm x0) (Rm x3) = true →
          ord2b (Rm x2) (Rm x3) = true →
            famOk (fun j => evalG (quadF (Rm x0) (Rm x1) (Rm x2) (Rm x3)) (wordsD j)) = true := by
  intro x0 hx0 x1 hx1 h01 x2 hx2 h12 h02 x3 hx3 h13 h03 h23
  exact chkD3_spec (chkD2_spec (chkD1_spec (chkD1_all x0 hx0) hx1 h01) hx2 h12 h02) hx3 h13 h03 h23

end CFSG.StandardType.F4Model
