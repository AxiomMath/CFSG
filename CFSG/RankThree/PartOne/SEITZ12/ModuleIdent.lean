module

public import CFSG.RankThree.PartOne.SEITZ12.ModuleDefs
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.RankThree.PartOne.SEITZ12.ColIdent

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

local macro "phi4ml_eval" : tactic =>
  `(tactic| simp only [polyEval, monoEval, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero, List.getD_cons_zero,
    List.getD_cons_succ])

@[expose] def phi4ml_vtSumWord : Word :=
  phi4ml_vtWord [[0], [10]] [[5], [15]] [[3], [13]] [[8], [18]] [[4], [14]] [[9], [19]]
    [[1], [11]] [[6], [16]] [[2], [12]] [[7], [17]]

theorem phi4ml_vtSumWord_check : collectCheck 20000 phi4ml_vtSumWord mulVtCoords = true := by
  decide +kernel

theorem phi4ml_mulVtWord_eq : mulVtWord =
    phi4ml_vtWord [[0]] [[5]] [[3]] [[8]] [[4]] [[9]] [[1]] [[6]] [[2]] [[7]] ++
      phi4ml_vtWord [[10]] [[15]] [[13]] [[18]] [[14]] [[19]] [[11]] [[16]] [[12]] [[17]] := rfl

theorem phi4ml_vt_mul (hK : Nat.card K = 2 ^ (2 * m + 1)) (e k l g i e' k' l' g' i' : K) :
    phi4ml_vt m K e k l g i * phi4ml_vt m K e' k' l' g' i' =
      phi4ml_vt m K (e + e') (k + k') (l + l') (g + g') (i + i') := by
  obtain ⟨σ, hσ, -⟩ := exists_sigma (m := m) hK
  have hchar : CharP K 2 := ‹CharP K F4.prime›
  let x : ℕ → K := fun n => [e, k, l, g, i, σ e, σ k, σ l, σ g, σ i, e', k', l', g', i', σ e',
    σ k', σ l', σ g', σ i'].getD n 0
  have h1 := wordEval_of_collectCheck (R := K) mulVt_check x
  have h2 := wordEval_of_collectCheck (R := K) phi4ml_vtSumWord_check x
  have hL : wordEval K x mulVtWord =
      phi4ml_vt m K e k l g i * phi4ml_vt m K e' k' l' g' i' := by
    rw [phi4ml_mulVtWord_eq, wordEval_append,
      phi4ml_wordEval_vtWord σ hσ x _ _ _ _ _ _ _ _ _ _ (by simp [polyEval, monoEval, x])
        (by simp [polyEval, monoEval, x]) (by simp [polyEval, monoEval, x])
        (by simp [polyEval, monoEval, x]) (by simp [polyEval, monoEval, x]),
      phi4ml_wordEval_vtWord σ hσ x _ _ _ _ _ _ _ _ _ _ (by simp [polyEval, monoEval, x])
        (by simp [polyEval, monoEval, x]) (by simp [polyEval, monoEval, x])
        (by simp [polyEval, monoEval, x]) (by simp [polyEval, monoEval, x])]
    simp [polyEval, monoEval, x]
  have hR : wordEval K x phi4ml_vtSumWord =
      phi4ml_vt m K (e + e') (k + k') (l + l') (g + g') (i + i') := by
    rw [phi4ml_vtSumWord, phi4ml_wordEval_vtWord σ hσ x _ _ _ _ _ _ _ _ _ _
      (by simp [polyEval, monoEval, x]) (by simp [polyEval, monoEval, x])
      (by simp [polyEval, monoEval, x]) (by simp [polyEval, monoEval, x])
      (by simp [polyEval, monoEval, x])]
    simp [polyEval, monoEval, x]
  rw [← hL, ← hR, h1, h2]

@[expose] def phi4ml_BWord : Word :=
  [(25, [[10]]), (27, [[11]]), (28, [[12]]), (30, [[10, 10, 11], [13]])]

theorem phi4ml_conjBVtWord_eq : conjBVtWord = phi4ml_BWord ++
    phi4ml_vtWord [[0]] [[5]] [[3]] [[8]] [[4]] [[9]] [[1]] [[6]] [[2]] [[7]] ++
      phi4ml_BWord.reverse := rfl

theorem phi4ml_wordEval_BWord (σ : K →+* K) (hσ : ∀ c, σ c = largeReeSigma m c) (x : ℕ → K)
    (h11 : x 11 = σ (x 10)) (h13 : x 13 = σ (x 12)) :
    wordEval K x phi4ml_BWord = sylowB m K (x 10) (x 12) := by
  simp only [wordEval, phi4ml_BWord, sylowB, sylowX, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, polyEval, monoEval, List.sum_cons, List.sum_nil, h11, h13, ← hσ,
    add_zero, mul_assoc]
  ring_nf

@[expose] def phi4ml_conjRhsWord : Word :=
  phi4ml_vtWord [[0]] [[5]]
    [[0, 10, 10, 11], [0, 10, 12], [0, 13], [1, 10, 11], [1, 12], [2, 10], [3]]
    [[5, 10, 10, 11, 11], [5, 11, 13], [5, 12, 12], [6, 10, 10, 11], [6, 13], [7, 11], [8]]
    [[4], [5, 10, 11], [5, 12], [6, 10]] [[0, 0, 10, 10, 11], [0, 0, 13], [1, 1, 11], [9]]
    [[0, 10], [1]] [[5, 11], [6]] [[0, 12], [1, 11], [2]] [[5, 13], [6, 10, 10], [7]]

theorem phi4ml_conjRhsWord_check : collectCheck 20000 phi4ml_conjRhsWord conjBVtCoords = true := by
  decide +kernel

theorem phi4ml_conj_B_vt (hK : Nat.card K = 2 ^ (2 * m + 1)) (b c e k l g i : K) :
    sylowB m K b c * phi4ml_vt m K e k l g i * (sylowB m K b c)⁻¹ =
      phi4ml_vt m K e (k + b * e) (l + largeReeSigma m b * k + c * e)
        (g + b * l + (b * largeReeSigma m b + c) * k +
          (b * c + b ^ 2 * largeReeSigma m b + largeReeSigma m c) * e)
        (i + (b * largeReeSigma m b + c) * largeReeSigma m e + b * largeReeSigma m k) := by
  obtain ⟨σ, hσ, hσσ⟩ := exists_sigma (m := m) hK
  have hchar : CharP K 2 := ‹CharP K F4.prime›
  let x : ℕ → K := fun n => [e, k, l, g, i, σ e, σ k, σ l, σ g, σ i, b, σ b, c, σ c].getD n 0
  have h1 := wordEval_of_collectCheck (R := K) conjBVt_check x
  have h2 := wordEval_of_collectCheck (R := K) phi4ml_conjRhsWord_check x
  have hL : wordEval K x conjBVtWord =
      sylowB m K b c * phi4ml_vt m K e k l g i * (sylowB m K b c)⁻¹ := by
    rw [phi4ml_conjBVtWord_eq, wordEval_append, wordEval_append,
      phi4ml_wordEval_reverse x phi4ml_BWord,
      phi4ml_wordEval_BWord σ hσ x (by simp [x]) (by simp [x]),
      phi4ml_wordEval_vtWord σ hσ x _ _ _ _ _ _ _ _ _ _ (by simp [polyEval, monoEval, x])
        (by simp [polyEval, monoEval, x]) (by simp [polyEval, monoEval, x])
        (by simp [polyEval, monoEval, x]) (by simp [polyEval, monoEval, x])]
    simp [polyEval, monoEval, x]
  have hR : wordEval K x phi4ml_conjRhsWord = phi4ml_vt m K e (k + b * e)
      (l + largeReeSigma m b * k + c * e)
      (g + b * l + (b * largeReeSigma m b + c) * k +
        (b * c + b ^ 2 * largeReeSigma m b + largeReeSigma m c) * e)
      (i + (b * largeReeSigma m b + c) * largeReeSigma m e + b * largeReeSigma m k) := by
    rw [phi4ml_conjRhsWord, phi4ml_wordEval_vtWord σ hσ x _ _ _ _ _ _ _ _ _ _
      (by simp [polyEval, monoEval, x])
      (by simp only [x]; phi4ml_eval; simp only [map_add, map_mul, hσσ]; ring)
      (by simp only [x]; phi4ml_eval; simp only [map_add, map_mul, hσσ]; ring)
      (by simp only [x]; phi4ml_eval; simp only [map_add, map_mul])
      (by simp only [x]; phi4ml_eval; simp only [map_add, map_mul, hσσ]; ring)]
    simp only [x]
    phi4ml_eval
    simp only [hσ]
    ring_nf
  rw [← hL, ← hR, h1, h2]

theorem phi4ml_sylowB_zero : sylowB m K 0 0 = 1 := by
  simp [sylowB, sylowX, largeReeSigma_zero, pinnedX_zero]

@[expose] def phi4ml_WWord : Word :=
  [(24, [[0]]), (33, [[10]]), (26, [[1]]), (34, [[11]]), (36, [[2]]), (39, [[1, 1, 11], [12]]),
    (29, [[3]]), (37, [[13]]), (43, [[4]]), (46, [[3, 3, 13], [14]]), (35, [[5]]), (32, [[15]]),
    (44, [[6]]), (47, [[5, 5, 15], [16]]), (31, [[7]]), (40, [[17]]), (38, [[8]]), (42, [[18]]),
    (41, [[9]]), (45, [[19]])]

@[expose] def phi4ml_HWord : Word := [(35, [[20]]), (32, [[21]]), (47, [[20, 20, 21]])]

theorem phi4ml_commV2HWord_eq : commV2HWord =
    phi4ml_WWord ++ phi4ml_HWord ++ phi4ml_WWord.reverse ++ phi4ml_HWord.reverse := rfl

section Comm

variable (σ : K →+* K) (hσ : ∀ c, σ c = largeReeSigma m c) (x : ℕ → K)
  (hx : ∀ n, n < 10 → x (10 + n) = σ (x n))

include hσ hx in
theorem phi4ml_wordEval_WWord :
    wordEval K x phi4ml_WWord =
      sylowV m K (x 0) 0 0 (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) := by
  have h10 := hx 0 (by norm_num)
  have h11 := hx 1 (by norm_num)
  have h12 := hx 2 (by norm_num)
  have h13 := hx 3 (by norm_num)
  have h14 := hx 4 (by norm_num)
  have h15 := hx 5 (by norm_num)
  have h16 := hx 6 (by norm_num)
  have h17 := hx 7 (by norm_num)
  have h18 := hx 8 (by norm_num)
  have h19 := hx 9 (by norm_num)
  simp only [wordEval, phi4ml_WWord, sylowV, sylowA, phi4ml_sylowB_zero, sylowD, sylowF, sylowH,
    sylowJ, sylowK, sylowL, sylowX, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, polyEval, monoEval, List.sum_cons, List.sum_nil, add_zero, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, ← hσ, mul_assoc]
  ring_nf

end Comm

theorem phi4ml_wordEval_HWord (σ : K →+* K) (hσ : ∀ c, σ c = largeReeSigma m c) (x : ℕ → K)
    (h21 : x 21 = σ (x 20)) : wordEval K x phi4ml_HWord = sylowH m K (x 20) 0 := by
  simp only [wordEval, phi4ml_HWord, sylowH, sylowX, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, polyEval, monoEval, List.sum_cons, List.sum_nil, add_zero, h21,
    ← hσ, map_zero, pinnedX_zero, mul_assoc]
  ring_nf

@[expose] def phi4ml_commRhsWord : Word :=
  phi4ml_vtWord [[0, 20]] [[10, 21]] [[7, 20]] [[17, 21]]
    [[0, 7, 20], [1, 3, 20], [5, 21], [15, 20]]
    [[5, 5, 21], [10, 17, 21], [11, 13, 21], [15, 20, 20]] [[1, 20]] [[11, 21]] [[3, 20]]
    [[13, 21]]

theorem phi4ml_commRhsWord_check : collectCheck 20000 phi4ml_commRhsWord commV2HCoords = true := by
  decide +kernel

theorem phi4ml_comm_H_vt (hK : Nat.card K = 2 ^ (2 * m + 1)) (a d e f g h₁ i₁ j k l h : K) :
    sylowV m K a 0 0 d e f g h₁ i₁ j k l * sylowH m K h 0 *
        (sylowV m K a 0 0 d e f g h₁ i₁ j k l)⁻¹ * (sylowH m K h 0)⁻¹ =
      phi4ml_vt m K (a * h) (d * h) (f * h) (j * h)
        (a * j * h + d * f * h + h₁ * largeReeSigma m h + largeReeSigma m h₁ * h) := by
  obtain ⟨σ, hσ, hσσ⟩ := exists_sigma (m := m) hK
  have hchar : CharP K 2 := ‹CharP K F4.prime›
  let x : ℕ → K := fun n => [a, d, e, f, g, h₁, i₁, j, k, l, σ a, σ d, σ e, σ f, σ g, σ h₁, σ i₁,
    σ j, σ k, σ l, h, σ h].getD n 0
  have hx : ∀ n, n < 10 → x (10 + n) = σ (x n) := by
    intro n hn
    interval_cases n <;> rfl
  have h1 := wordEval_of_collectCheck (R := K) commV2H_check x
  have h2 := wordEval_of_collectCheck (R := K) phi4ml_commRhsWord_check x
  have hL : wordEval K x commV2HWord =
      sylowV m K a 0 0 d e f g h₁ i₁ j k l * sylowH m K h 0 *
        (sylowV m K a 0 0 d e f g h₁ i₁ j k l)⁻¹ * (sylowH m K h 0)⁻¹ := by
    rw [phi4ml_commV2HWord_eq, wordEval_append, wordEval_append, wordEval_append,
      phi4ml_wordEval_reverse x phi4ml_WWord, phi4ml_wordEval_reverse x phi4ml_HWord,
      phi4ml_wordEval_WWord σ hσ x hx, phi4ml_wordEval_HWord σ hσ x (by simp [x])]
    rfl
  have hR : wordEval K x phi4ml_commRhsWord = phi4ml_vt m K (a * h) (d * h) (f * h) (j * h)
      (a * j * h + d * f * h + h₁ * largeReeSigma m h + largeReeSigma m h₁ * h) := by
    rw [phi4ml_commRhsWord, phi4ml_wordEval_vtWord σ hσ x _ _ _ _ _ _ _ _ _ _
      (by simp only [x]; phi4ml_eval; simp only [map_mul])
      (by simp only [x]; phi4ml_eval; simp only [map_mul])
      (by simp only [x]; phi4ml_eval; simp only [map_add, map_mul, hσσ]; ring)
      (by simp only [x]; phi4ml_eval; simp only [map_mul])
      (by simp only [x]; phi4ml_eval; simp only [map_mul])]
    simp only [x]
    phi4ml_eval
    simp only [hσ]
    ring_nf
  rw [← hL, ← hR, h1, h2]

@[expose] def phi4ml_HiWord : Word := [(44, [[22]]), (47, [[23]])]

@[expose] def phi4ml_HsplitWord1 : Word := phi4ml_HWord ++ phi4ml_HiWord

@[expose] def phi4ml_HsplitWord2 : Word :=
  [(35, [[20]]), (32, [[21]]), (44, [[22]]), (47, [[20, 20, 21], [23]])]

@[expose] def phi4ml_HsplitCoords : List Poly :=
  [[], [], [], [], [], [], [], [], [[21]], [], [], [[20]], [], [], [], [], [], [], [], [],
    [[20, 21], [22]], [], [], [[23]]]

theorem phi4ml_HsplitWord1_check :
    collectCheck 1000 phi4ml_HsplitWord1 phi4ml_HsplitCoords = true := by
  decide +kernel

theorem phi4ml_HsplitWord2_check :
    collectCheck 1000 phi4ml_HsplitWord2 phi4ml_HsplitCoords = true := by
  decide +kernel

theorem phi4ml_sylowH_split (hK : Nat.card K = 2 ^ (2 * m + 1)) (h i : K) :
    sylowH m K h i = sylowH m K h 0 * sylowH m K 0 i := by
  obtain ⟨σ, hσ, -⟩ := exists_sigma (m := m) hK
  have hchar : CharP K 2 := ‹CharP K F4.prime›
  let x : ℕ → K := fun n =>
    if n = 20 then h else if n = 21 then σ h else if n = 22 then i else if n = 23 then σ i else 0
  have h1 := wordEval_of_collectCheck (R := K) phi4ml_HsplitWord1_check x
  have h2 := wordEval_of_collectCheck (R := K) phi4ml_HsplitWord2_check x
  have hL : wordEval K x phi4ml_HsplitWord1 = sylowH m K h 0 * sylowH m K 0 i := by
    rw [phi4ml_HsplitWord1, wordEval_append, phi4ml_wordEval_HWord σ hσ x (by simp [x])]
    simp only [wordEval, phi4ml_HiWord, sylowH, sylowX, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, polyEval, monoEval, List.sum_cons, List.sum_nil,
      add_zero, ← hσ, map_zero, pinnedX_zero, mul_assoc]
    simp [x]
  have hR : wordEval K x phi4ml_HsplitWord2 = sylowH m K h i := by
    simp only [wordEval, phi4ml_HsplitWord2, sylowH, sylowX, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, polyEval, monoEval, List.sum_cons, List.sum_nil,
      add_zero, mul_assoc]
    simp [x, ← hσ]
    ring_nf
  rw [← hR, ← hL, h1, h2]

end CFSG.RankThree.PartOne.SEITZ12
