module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Ree.LargeReeInvolutionFusion

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Chevalley.RootOps (orbitCertRoot)

open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom f4i torusWeight torusWeight_apply torusExp0
  torusPair_conj_pinnedX)


namespace LeviRat

theorem sylowWord_vars : ∀ f ∈ sylowWord, ∀ mm ∈ f.2, ∀ i ∈ mm, i < 24 := by
  decide +kernel

@[expose] def abaWord : Word :=
  [(24, [[0]]), (33, [[12]]), (25, [[]]), (27, [[]]), (30, [[]]), (33, [[12]]), (24, [[0]])]

@[expose] def abaCoords : List Poly :=
  [[], [[]], [[0]], [[]], [], [], [[]], [[0]], [[0, 0]], [], [[12]], [], [], [[12]], [[0, 12]],
    [[0, 0, 12]], [[12]], [[0, 12]], [[0, 0, 12]], [], [], [], [], []]

@[expose] def abaSubst : List (ℕ × Poly) :=
  [(0, []), (12, []), (1, [[]]), (13, [[]]), (2, []), (14, []), (3, [[0]]), (15, [[12]]),
    (4, []), (16, []), (5, [[0]]), (17, [[12]]), (6, []), (18, []), (7, []), (19, []), (8, []),
    (20, []), (9, [[0]]), (21, [[12]]), (10, [[0, 12]]), (22, [[0, 0, 12]]), (11, []), (23, [])]

theorem aba_check : collectCheck 500 abaWord abaCoords = true := by decide +kernel

theorem abaV_check : collectCheck 2000
    (sylowWord.map fun q => (q.1, polySubst (substOf abaSubst) q.2)) abaCoords = true := by
  decide +kernel

@[expose] def bWord : Word :=
  [(25, [[1]]), (27, [[13]]), (28, [[2]]), (30, [[1, 1, 13], [14]])]

@[expose] def bInvWord : Word :=
  [(30, [[1, 1, 13], [14]]), (28, [[2]]), (27, [[13]]), (25, [[1]])]

@[expose] def fOneWord : Word :=
  [(29, [[]]), (37, [[]]), (46, [[]])]

@[expose] def dOneWord : Word :=
  [(26, [[]]), (34, [[]]), (39, [[]])]

@[expose] def bfbCoords : List Poly :=
  [[], [], [], [], [], [[]], [], [[1]], [], [], [], [], [], [[]], [], [], [[13]], [], [], [], [],
    [], [[]], []]

@[expose] def bfbSubst : List (ℕ × Poly) :=
  [(0, []), (12, []), (1, []), (13, []), (2, []), (14, []), (3, []), (15, []), (4, []), (16, []),
    (5, [[]]), (17, [[]]), (6, []), (18, []), (7, []), (19, []), (8, []), (20, []), (9, [[1]]),
    (21, [[13]]), (10, []), (22, []), (11, []), (23, [])]

theorem bfb_check : collectCheck 2000 (bWord ++ fOneWord ++ bInvWord) bfbCoords = true := by
  decide +kernel

theorem bfbV_check : collectCheck 2000
    (sylowWord.map fun q => (q.1, polySubst (substOf bfbSubst) q.2)) bfbCoords = true := by
  decide +kernel

@[expose] def bdbCoords : List Poly :=
  [[], [], [[]], [], [], [[13]], [], [[1, 13], [2]], [[13]], [], [[]], [[1]], [], [[1, 1]], [],
    [[]], [[1, 1, 13], [14]], [], [[13]], [], [[1, 13], [2]], [[14]],
    [[1, 1, 13, 13], [2, 2], [13, 14]], [[1, 1, 13], [14]]]

@[expose] def bdbSubst : List (ℕ × Poly) :=
  [(0, []), (12, []), (1, []), (13, []), (2, []), (14, []), (3, [[]]), (15, [[]]), (4, []),
    (16, []), (5, [[13]]), (17, [[1, 1]]), (6, [[1, 1, 13], [1, 2]]),
    (18, [[1, 1, 13, 13], [13, 14]]), (7, [[1]]), (19, [[13]]), (8, [[2]]), (20, [[14]]),
    (9, [[1, 13], [2]]), (21, [[1, 1, 13], [14]]), (10, []), (22, []), (11, [[1, 13], [2]]),
    (23, [[1, 1, 13], [14]])]

theorem bdb_check : collectCheck 2000 (bWord ++ dOneWord ++ bInvWord) bdbCoords = true := by
  decide +kernel

theorem bdbV_check : collectCheck 2000
    (sylowWord.map fun q => (q.1, polySubst (substOf bdbSubst) q.2)) bdbCoords = true := by
  decide +kernel

section Words

variable {K : Type} [Field K] [CharP K F4.prime] {m : ℕ}

theorem sylowX_inv (r : ℕ) (c : K) :
    (sylowX K r c)⁻¹ = sylowX K r c := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [sylowX, pinnedX_neg, CharTwo.neg_eq]

theorem wordEval_eq_sylowV {n n' : ℕ} {w : Word} {T : List Poly}
    (φ : List (ℕ × Poly)) (hw : collectCheck n w T = true)
    (hv : collectCheck n' (sylowWord.map fun q => (q.1, polySubst (substOf φ) q.2)) T = true)
    (x : ℕ → K) (a b c d e f g h i j k l : K)
    (hφ : ∀ n < 24, polyEval x (substOf φ n) = coordVal m a b c d e f g h i j k l n) :
    wordEval K x w = sylowV m K a b c d e f g h i j k l := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [sylowV_eq_wordEval]
  have h1 : wordEval K (coordVal m a b c d e f g h i j k l) sylowWord =
      wordEval K x (sylowWord.map fun q => (q.1, polySubst (substOf φ) q.2)) := by
    simp only [wordEval, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun q hq => ?_)
    have hpe : polyEval (coordVal m a b c d e f g h i j k l) q.2 =
        polyEval x (polySubst (substOf φ) q.2) := by
      rw [polyEval_polySubst]
      exact polyEval_congr fun mm hm i hi => (hφ i (sylowWord_vars q hq mm hm i hi)).symm
    simp only [Function.comp_apply, hpe]
  rw [h1]
  exact (wordEval_eq_iff hw hv x).2 fun _ => rfl

theorem largeReeSigma_add (x y : K) :
    largeReeSigma m (x + y) = largeReeSigma m x + largeReeSigma m y := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have e : 2 * 2 ^ m = 2 ^ (m + 1) := by ring
  simp only [largeReeSigma, e]
  exact add_pow_char_pow x y 2 (m + 1)

omit [CharP K F4.prime] in
theorem wordEval_eq_prod_sylowX
    (x : ℕ → K) (w : Word) :
    wordEval K x w = (w.map fun q => sylowX K q.1 (polyEval x q.2)).prod :=
  rfl

omit [CharP K F4.prime] in
theorem wordEval_bWord
    (x : ℕ → K) (b c : K) (hb : x 1 = b) (hc : x 2 = c)
    (hb' : x 13 = largeReeSigma m b) (hc' : x 14 = largeReeSigma m c) :
    wordEval K x bWord = sylowB m K b c := by
  have e30 : polyEval x [[1, 1, 13], [14]] = largeReeSigma m c + b ^ 2 * largeReeSigma m b := by
    simp only [polyEval, monoEval, hb, hb', hc', List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, List.sum_cons, List.sum_nil, add_zero]
    ring
  have e25 : polyEval x [[1]] = b := by simp [polyEval, monoEval, hb]
  have e27 : polyEval x [[13]] = largeReeSigma m b := by simp [polyEval, monoEval, hb']
  have e28 : polyEval x [[2]] = c := by simp [polyEval, monoEval, hc]
  simp only [wordEval_eq_prod_sylowX, bWord, sylowB, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, e25, e27, e28, e30, mul_assoc]

theorem wordEval_bInvWord
    (x : ℕ → K) (b c : K) (hb : x 1 = b) (hc : x 2 = c)
    (hb' : x 13 = largeReeSigma m b) (hc' : x 14 = largeReeSigma m c) :
    wordEval K x bInvWord = (sylowB m K b c)⁻¹ := by
  rw [← wordEval_bWord x b c hb hc hb' hc']
  simp only [wordEval_eq_prod_sylowX, bWord, bInvWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_inv_rev, sylowX_inv, mul_assoc]

omit [CharP K F4.prime] in
theorem wordEval_fOneWord
    (x : ℕ → K) : wordEval K x fOneWord = sylowF m K 1 0 := by
  simp [wordEval_eq_prod_sylowX, fOneWord, sylowF, sylowX, polyEval, monoEval, largeReeSigma_one,
    largeReeSigma_zero, pinnedX_zero, mul_assoc]

omit [CharP K F4.prime] in
theorem wordEval_dOneWord
    (x : ℕ → K) : wordEval K x dOneWord = sylowD m K 1 0 := by
  simp [wordEval_eq_prod_sylowX, dOneWord, sylowD, sylowX, polyEval, monoEval, largeReeSigma_one,
    largeReeSigma_zero, pinnedX_zero, mul_assoc]

omit [CharP K F4.prime] in
theorem sylowV_f_j (f j : K) :
    sylowV m K 0 0 0 0 0 f 0 0 0 j 0 0 = sylowF m K f 0 * sylowJ m K j := by
  simp [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowH, sylowK_zero, sylowL,
    sylowX, largeReeSigma_zero, pinnedX_zero]

variable [Finite K]

theorem sylowA_mul_sylowB_one_mul_inv
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : K) :
    sylowA m K s * sylowB m K 1 0 * (sylowA m K s)⁻¹ =
      sylowV m K 0 1 0 s 0 s 0 0 0 s (s * largeReeSigma m s) 0 := by
  have hσσ := largeReeSigma_sigma hK s
  have h := wordEval_eq_sylowV (m := m) abaSubst aba_check abaV_check
    (coordVal m s 0 0 0 0 0 0 0 0 0 0 0) 0 1 0 s 0 s 0 0 0 s (s * largeReeSigma m s) 0 (by
      intro n hn
      interval_cases n <;>
        simp [abaSubst, substOf, List.lookup, polyEval, monoEval, coordVal, largeReeSigma_zero,
          largeReeSigma_one, largeReeSigma_mul, hσσ]
      ring)
  rw [← h]
  have e1 : wordEval K (coordVal m s 0 0 0 0 0 0 0 0 0 0 0) abaWord =
      sylowX K 24 s * sylowX K 33 (largeReeSigma m s) * sylowX K 25 1 * sylowX K 27 1 *
        sylowX K 30 1 * sylowX K 33 (largeReeSigma m s) * sylowX K 24 s := by
    simp [wordEval, abaWord, sylowX, polyEval, monoEval, coordVal, mul_assoc]
  rw [e1, sylowA, sylowB_one_zero, mul_inv_rev, sylowX_inv, sylowX_inv]
  simp only [mul_assoc]

omit [Finite K] in
theorem sylowB_mul_sylowF_one_mul_inv (b c : K) :
    sylowB m K b c * sylowF m K 1 0 * (sylowB m K b c)⁻¹ = sylowF m K 1 0 * sylowJ m K b := by
  have h := wordEval_eq_sylowV (m := m) bfbSubst bfb_check bfbV_check
    (coordVal m 0 b c 0 0 0 0 0 0 0 0 0) 0 0 0 0 0 1 0 0 0 b 0 0 (by
      intro n hn
      interval_cases n <;>
        simp [bfbSubst, substOf, List.lookup, polyEval, monoEval, coordVal, largeReeSigma_zero,
          largeReeSigma_one])
  rw [wordEval_append, wordEval_append, wordEval_bWord _ b c rfl rfl rfl rfl, wordEval_fOneWord,
    wordEval_bInvWord _ b c rfl rfl rfl rfl, sylowV_f_j] at h
  exact h

theorem sylowB_mul_sylowD_one_mul_inv
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (b c : K) :
    sylowB m K b c * sylowD m K 1 0 * (sylowB m K b c)⁻¹ =
      sylowV m K 0 0 0 1 0 (largeReeSigma m b) (b ^ 2 * largeReeSigma m b + b * c) b c
        (b * largeReeSigma m b + c) 0 (b * largeReeSigma m b + c) := by
  have hσσ := largeReeSigma_sigma hK b
  have h := wordEval_eq_sylowV (m := m) bdbSubst bdb_check bdbV_check
    (coordVal m 0 b c 0 0 0 0 0 0 0 0 0) 0 0 0 1 0 (largeReeSigma m b)
    (b ^ 2 * largeReeSigma m b + b * c) b c (b * largeReeSigma m b + c) 0
    (b * largeReeSigma m b + c) (by
      intro n hn
      interval_cases n <;>
        simp [bdbSubst, substOf, List.lookup, polyEval, monoEval, coordVal, largeReeSigma_zero,
          largeReeSigma_one, largeReeSigma_mul, largeReeSigma_add, hσσ, pow_two] <;> ring)
  rw [wordEval_append, wordEval_append, wordEval_bWord _ b c rfl rfl rfl rfl, wordEval_dOneWord,
    wordEval_bInvWord _ b c rfl rfl rfl rfl] at h
  exact h

omit [Finite K] in
theorem sylowA_commute_sylowD (s d e : K) :
    Commute (sylowA m K s) (sylowD m K d e) := by
  rw [sylowA, sylowD]
  refine Commute.mul_left
    (Commute.mul_right (Commute.mul_right (Commute.mul_right ?_ ?_) ?_) ?_)
    (Commute.mul_right (Commute.mul_right (Commute.mul_right ?_ ?_) ?_) ?_) <;>
    exact sylowX_commute_of_commFactors (by norm_num) (by norm_num) (by norm_num) (by decide) _ _

omit [Finite K] in
theorem sylowB_commute_sylowJ (b c j : K) :
    Commute (sylowB m K b c) (sylowJ m K j) := by
  rw [sylowB, sylowJ]
  refine Commute.mul_left (Commute.mul_left (Commute.mul_left (Commute.mul_right ?_ ?_)
    (Commute.mul_right ?_ ?_)) (Commute.mul_right ?_ ?_)) (Commute.mul_right ?_ ?_) <;>
    exact sylowX_commute_of_commFactors (by norm_num) (by norm_num) (by norm_num) (by decide) _ _

omit [Finite K] [CharP K F4.prime] in
theorem cartanPair_B_one_three :
    (F4.cartanPair (f4i 0) (orbitCertRoot F4.tag 25) = 0 ∧
      F4.cartanPair (f4i 3) (orbitCertRoot F4.tag 25) = -1) ∧
    (F4.cartanPair (f4i 0) (orbitCertRoot F4.tag 27) = -1 ∧
      F4.cartanPair (f4i 3) (orbitCertRoot F4.tag 27) = 0) := by
  decide +kernel

omit [CharP K F4.prime] in
theorem torusOne_conj_sylowB_gen
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : Kˣ) (b c : K) :
    pairedTorusHom m (f4i 0) (f4i 3) s * sylowB m K b c * (pairedTorusHom m (f4i 0) (f4i 3) s)⁻¹ =
      sylowB m K (((s ^ (-(2 : ℤ) ^ m) : Kˣ) : K) * b)
        (((s ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) * c) := by
  obtain ⟨-, -, ⟨h0, -, -, h3⟩, ⟨h0', -, -, h3'⟩, -⟩ := cartanPair_A_B
  obtain ⟨⟨h25_0, h25_3⟩, ⟨h27_0, h27_3⟩⟩ := cartanPair_B_one_three
  have w25 : torusWeight m (orbitCertRoot F4.tag 25) (s, 1) = s ^ (-(2 : ℤ) ^ m) := by
    rw [torusWeight_apply, one_zpow, mul_one]
    simp only [torusExp0]
    rw [h25_0, h25_3]
    congr 1
    ring
  have w27 : ((torusWeight m (orbitCertRoot F4.tag 27) (s, 1) : Kˣ) : K) =
      largeReeSigma m (((s ^ (-(2 : ℤ) ^ m) : Kˣ) : K)) := by
    rw [torusWeight_apply, one_zpow, mul_one, largeReeSigma, ← Units.val_pow_eq_pow_val,
      ← zpow_natCast, ← zpow_mul]
    simp only [torusExp0]
    rw [h27_0, h27_3]
    congr 1
    refine units_zpow_congr hK s 1 ?_
    push_cast
    rw [show ((2 : ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 by ring]
    ring
  have w28 : torusWeight m (orbitCertRoot F4.tag 28) (s, 1) = s ^ ((-1 : ℤ) - 2 ^ m) := by
    rw [torusWeight_apply, one_zpow, mul_one]
    simp only [torusExp0]
    rw [h0, h3]
    ring_nf
  have w30 : ((torusWeight m (orbitCertRoot F4.tag 30) (s, 1) : Kˣ) : K) =
      largeReeSigma m (((s ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K)) := by
    rw [torusWeight_apply, one_zpow, mul_one, largeReeSigma, ← Units.val_pow_eq_pow_val,
      ← zpow_natCast, ← zpow_mul]
    simp only [torusExp0]
    rw [h0', h3']
    congr 1
    refine units_zpow_congr hK s 1 ?_
    push_cast
    rw [show ((2 : ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 by ring]
    ring
  have w30' : ((torusWeight m (orbitCertRoot F4.tag 30) (s, 1) : Kˣ) : K) =
      (((s ^ (-(2 : ℤ) ^ m) : Kˣ) : K)) ^ 2 * largeReeSigma m (((s ^ (-(2 : ℤ) ^ m) : Kˣ) : K)) := by
    rw [torusWeight_apply, one_zpow, mul_one, largeReeSigma, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
      ← zpow_mul, ← zpow_add]
    simp only [torusExp0]
    rw [h0', h3']
    congr 1
    refine units_zpow_congr hK s 1 ?_
    push_cast
    rw [show ((2 : ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 by ring]
    ring
  rw [← rankOneTorusPair_left, sylowB, sylowB, sylowX, sylowX, sylowX, sylowX, weyl_conj_mul,
    weyl_conj_mul, weyl_conj_mul,
    torusPair_conj_pinnedX m (s, 1) (sylowRoot_pos (r := 25) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX m (s, 1) (sylowRoot_pos (r := 27) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX m (s, 1) (sylowRoot_pos (r := 28) (by norm_num) (by norm_num)).1,
    torusPair_conj_pinnedX m (s, 1) (sylowRoot_pos (r := 30) (by norm_num) (by norm_num)).1,
    w25, w28, w27, largeReeSigma_mul]
  have e30 : ((torusWeight m (orbitCertRoot F4.tag 30) (s, 1) : Kˣ) : K) *
      (largeReeSigma m c + b ^ 2 * largeReeSigma m b) =
      largeReeSigma m (((s ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K)) * largeReeSigma m c +
        (((s ^ (-(2 : ℤ) ^ m) : Kˣ) : K) * b) ^ 2 *
          (largeReeSigma m (((s ^ (-(2 : ℤ) ^ m) : Kˣ) : K)) * largeReeSigma m b) := by
    rw [← w30]
    linear_combination (b ^ 2 * largeReeSigma m b) * w30'
  rw [e30]
  simp only [sylowX, largeReeSigma_mul]

end Words

end LeviRat

end CFSG.RankThree.PartOne.SEITZRF
