module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43ClassCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Code

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res4.U43

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43

@[expose] def codeX : List (List ℕ) :=
  [[5, 8, 8, 6, 5, 4, 1, 8, 5, 1, 4, 8, 3, 5, 5, 5],
    [4, 6, 8, 8, 3, 4, 7, 7, 5, 4, 5, 2, 5, 4, 2, 5],
    [3, 8, 5, 8, 5, 3, 4, 7, 8, 7, 4, 2, 5, 4, 2, 5],
    [4, 3, 7, 5, 6, 4, 8, 4, 4, 5, 5, 1, 8, 7, 1, 5]]

@[expose] def cX (k : ℕ) : List ℕ := codeX.getD k []

theorem uAt_basis : ∀ k < 4, uAt (uLiftBasis.getD k 0) = cX k := by
  decide +kernel

@[expose] def rtProdL (e : ℕ) : List ℕ :=
  mul4 (mul4 (mul4 (pow4 (cX 0) (e % 3)) (pow4 (cX 1) (e / 3 % 3))) (pow4 (cX 2) (e / 9 % 3)))
    (pow4 (cX 3) (e / 27 % 3))

theorem rtProd_eq (e : ℕ) : rtProd e = rtProdL e := by
  rw [rtProd, rtProdL, uAt_basis 0 (by norm_num), uAt_basis 1 (by norm_num),
    uAt_basis 2 (by norm_num), uAt_basis 3 (by norm_num)]

@[expose] def codeG1 : List ℕ := [8, 4, 7, 3, 5, 6, 0, 3, 6, 8, 6, 0, 7, 7, 3, 4]

@[expose] def codeG2 : List ℕ := [3, 5, 5, 4, 8, 4, 5, 2, 8, 8, 3, 7, 7, 2, 4, 5]

theorem wordCode_gen : wordCode (uGenWords.getD 1 []) = codeG1 ∧
    wordCode (uGenWords.getD 2 []) = codeG2 := by
  decide +kernel

theorem gen_words_ok : (∀ l ∈ uGenWords.getD 1 [], l < 4) ∧ ∀ l ∈ uGenWords.getD 2 [], l < 4 := by
  decide

@[expose] def codeQ (a b : ℕ) : List ℕ := mul4 (pow4 codeG1 a) (pow4 codeG2 b)

@[expose] def sigList : List (List ℕ) :=
  [[5, 8, 8, 6, 5, 4, 1, 8, 5, 1, 4, 8, 3, 5, 5, 5],
    [4, 3, 7, 5, 6, 4, 8, 4, 4, 5, 5, 1, 8, 7, 1, 5],
    [4, 7, 5, 6, 4, 5, 1, 7, 8, 1, 5, 5, 3, 4, 8, 4],
    [5, 2, 6, 0, 2, 5, 6, 0, 3, 3, 5, 0, 0, 0, 0, 3],
    [3, 0, 0, 0, 0, 4, 6, 1, 0, 3, 4, 3, 0, 1, 6, 4],
    [5, 7, 2, 8, 4, 4, 4, 6, 2, 7, 5, 8, 5, 3, 5, 4],
    [4, 8, 2, 7, 5, 5, 7, 6, 2, 4, 4, 5, 4, 3, 8, 5],
    [4, 0, 6, 2, 0, 3, 0, 0, 3, 0, 4, 6, 2, 0, 3, 4],
    [5, 1, 0, 2, 1, 5, 0, 1, 0, 0, 3, 0, 2, 1, 0, 5]]

@[expose] def sig (a b : ℕ) : List ℕ := sigList.getD (3 * a + b) []

theorem sig_check : ∀ a < 3, ∀ b < 3, mul4 (sig a b) (codeQ a b) = mul4 (codeQ a b) (cX 0) := by
  decide +kernel

theorem sig_canon : ∀ a < 3, ∀ b < 3, canon4 (sig a b) = true := by
  decide +kernel

@[expose] def sigInjB : Bool :=
  (List.range 3).all fun a => (List.range 3).all fun b => (List.range 3).all fun a₁ =>
    (List.range 3).all fun b₁ => sig a b != sig a₁ b₁ || (a == a₁ && b == b₁)

theorem sigInjB_eq : sigInjB = true := by
  decide +kernel

theorem sig_inj {a b a₁ b₁ : ℕ} (ha : a < 3) (hb : b < 3) (ha₁ : a₁ < 3) (hb₁ : b₁ < 3)
    (h : sig a b = sig a₁ b₁) : a = a₁ ∧ b = b₁ := by
  have := sigInjB_eq
  simp only [sigInjB, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.and_eq_true, beq_iff_eq] at this
  rcases this a ha b hb a₁ ha₁ b₁ hb₁ with h1 | h1
  · exact absurd h h1
  · exact h1

@[expose] def wIdx (a b : ℕ) : ℕ := if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then 3 else 2

@[expose] def wCheckB : Bool :=
  (List.range 3).all fun a => (List.range 3).all fun b => (a == 0 && b == 0) ||
    (List.range 3).all fun i => (List.range 3).all fun j => (i == 0 && j == 0) ||
      !commutes4 (mul4 (pow4 (cX 0) i) (pow4 (cX (wIdx a b)) j)) (codeQ a b)

theorem wCheckB_eq : wCheckB = true := by
  decide +kernel

theorem w_check {a b i j : ℕ} (ha : a < 3) (hb : b < 3) (hab : ¬ (a = 0 ∧ b = 0)) (hi : i < 3)
    (hj : j < 3) (hij : ¬ (i = 0 ∧ j = 0)) :
    commutes4 (mul4 (pow4 (cX 0) i) (pow4 (cX (wIdx a b)) j)) (codeQ a b) = false := by
  have := wCheckB_eq
  simp only [wCheckB, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at this
  rcases this a ha b hb with h | h
  · exact absurd h hab
  · rcases h i hi j hj with h2 | h2
    · exact absurd h2 hij
    · exact h2

theorem z_check : ∀ i < 3, ∀ j < 3, ∀ k < 3, ¬ (i = 0 ∧ j = 0 ∧ k = 0) →
    (commutes4 (mul4 (mul4 (pow4 (cX 0) i) (pow4 (cX 2) j)) (pow4 (cX 3) k)) (codeQ 1 0) &&
      commutes4 (mul4 (mul4 (pow4 (cX 0) i) (pow4 (cX 2) j)) (pow4 (cX 3) k)) (codeQ 0 1)) =
      false := by
  decide +kernel

@[expose] def dist2B : Bool :=
  [2, 3].all fun m => (List.range 3).all fun i => (List.range 3).all fun j =>
    (List.range 3).all fun i₁ => (List.range 3).all fun j₁ =>
      mul4 (pow4 (cX 0) i) (pow4 (cX m) j) != mul4 (pow4 (cX 0) i₁) (pow4 (cX m) j₁) ||
        (i == i₁ && j == j₁)

theorem dist2B_eq : dist2B = true := by
  decide +kernel

theorem dist2 {m i j i₁ j₁ : ℕ} (hm : m = 2 ∨ m = 3) (hi : i < 3) (hj : j < 3) (hi₁ : i₁ < 3)
    (hj₁ : j₁ < 3)
    (h : mul4 (pow4 (cX 0) i) (pow4 (cX m) j) = mul4 (pow4 (cX 0) i₁) (pow4 (cX m) j₁)) :
    i = i₁ ∧ j = j₁ := by
  have := dist2B_eq
  simp only [dist2B, List.all_eq_true, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq] at this
  rcases this m hm i hi j hj i₁ hi₁ j₁ hj₁ with h1 | h1
  · exact absurd h h1
  · exact h1

@[expose] def dist3B : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j => (List.range 3).all fun k =>
    (List.range 3).all fun i₁ => (List.range 3).all fun j₁ => (List.range 3).all fun k₁ =>
      mul4 (mul4 (pow4 (cX 0) i) (pow4 (cX 2) j)) (pow4 (cX 3) k) !=
          mul4 (mul4 (pow4 (cX 0) i₁) (pow4 (cX 2) j₁)) (pow4 (cX 3) k₁) ||
        (i == i₁ && j == j₁ && k == k₁)

theorem dist3B_eq : dist3B = true := by
  decide +kernel

theorem dist3 {i j k i₁ j₁ k₁ : ℕ} (hi : i < 3) (hj : j < 3) (hk : k < 3) (hi₁ : i₁ < 3)
    (hj₁ : j₁ < 3) (hk₁ : k₁ < 3)
    (h : mul4 (mul4 (pow4 (cX 0) i) (pow4 (cX 2) j)) (pow4 (cX 3) k) =
      mul4 (mul4 (pow4 (cX 0) i₁) (pow4 (cX 2) j₁)) (pow4 (cX 3) k₁)) :
    i = i₁ ∧ j = j₁ ∧ k = k₁ := by
  have := dist3B_eq
  simp only [dist3B, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.and_eq_true, beq_iff_eq] at this
  rcases this i hi j hj k hk i₁ hi₁ j₁ hj₁ k₁ hk₁ with h1 | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h h1
  · exact ⟨h1, h2, h3⟩

@[expose] def codeH0 : List ℕ := [8, 4, 7, 2, 2, 8, 4, 5, 8, 3, 5, 4, 4, 4, 3, 5]

@[expose] def codeH1 : List ℕ := [3, 2, 6, 1, 0, 2, 2, 5, 2, 0, 6, 8, 7, 4, 6, 7]

theorem wordCode_lift : wordCode (uLiftG.getD 0 []) = codeH0 ∧
    wordCode (uLiftG.getD 1 []) = codeH1 := by
  decide +kernel

theorem lift_words_ok : (∀ l ∈ uLiftG.getD 0 [], l < 4) ∧ ∀ l ∈ uLiftG.getD 1 [], l < 4 := by
  decide

@[expose] def codeT : List ℕ := [2, 7, 1, 0, 4, 1, 0, 6, 1, 0, 1, 4, 0, 3, 7, 2]

@[expose] def codeNegOne : List ℕ := [6, 0, 0, 0, 0, 6, 0, 0, 0, 0, 6, 0, 0, 0, 0, 6]

theorem codeT_eq :
    mul4 (mul4 (mul4 (mul4 (mul4 codeH0 codeH1) codeH1) codeH0) codeH1) codeH1 = codeT := by
  decide +kernel

theorem codeT_sq : mul4 codeT codeT = codeNegOne := by
  decide +kernel

@[expose] def imgE (k : ℕ) : ℕ := [79, 10, 44, 27].getD k 0

theorem img_check : ∀ k < 4, mul4 (rtProdL (imgE k)) codeT = mul4 codeT (cX k) := by
  decide +kernel

@[expose] def dE (i : ℕ) : ℕ := [27, 13, 39, 46].getD i 0

theorem diag_fix : ∀ i < 2, mul4 (rtProdL (dE i)) codeT = mul4 codeT (rtProdL (dE i)) := by
  decide +kernel

theorem diag_inv : ∀ i < 2, mul4 (sq4 (rtProdL (dE (i + 2)))) codeT =
    mul4 codeT (rtProdL (dE (i + 2))) := by
  decide +kernel

@[expose] def xCoeff (k i : ℕ) : ℕ :=
  ([[1, 1, 2, 0], [0, 2, 2, 1], [2, 1, 2, 2], [1, 0, 0, 0]].getD k []).getD i 0

theorem basis_check : ∀ k < 4, cX k = mul4 (mul4 (mul4 (pow4 (rtProdL (dE 0)) (xCoeff k 0))
    (pow4 (rtProdL (dE 1)) (xCoeff k 1))) (pow4 (rtProdL (dE 2)) (xCoeff k 2)))
    (pow4 (rtProdL (dE 3)) (xCoeff k 3)) := by
  decide +kernel

theorem dec4_negOne :
    dec4 codeNegOne = Matrix.scalar (Fin 4) (-1 : CFSG.LieType.Multipliers.U43.F9) := by
  decide +kernel

theorem dec4_codeT_01 : dec4 codeT 0 1 ≠ 0 := by
  decide +kernel

end CFSG.RankThree.PartTwo.Sec6.Res611Res4.U43
