module

public import CFSG.LocalAnalysis.StandardType.GGForkIndefLattice

public section

namespace CFSG.StandardType

section Lattice

@[expose] def ggAffineWord {N : Type} (ψγ : List N) (kγ a : N) (m : ℕ) : List N :=
  (List.replicate m (ψγ ++ [kγ] ++ ψγ.reverse ++ [a])).flatten

private def afp_pair {N : Type} [Fintype N] (X : Matrix N N ℤ) (c m : N → ℤ) : ℤ :=
  ∑ i, c i * ∑ j, X i j * m j

private lemma afp_pair_add {N : Type} [Fintype N] (X : Matrix N N ℤ) (c m m' : N → ℤ) :
    afp_pair X c (m + m') = afp_pair X c m + afp_pair X c m' := by
  simp only [afp_pair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma afp_pair_add_left {N : Type} [Fintype N] (X : Matrix N N ℤ) (c c' m : N → ℤ) :
    afp_pair X (c + c') m = afp_pair X c m + afp_pair X c' m := by
  simp only [afp_pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma afp_pair_smul {N : Type} [Fintype N] (X : Matrix N N ℤ) (c : N → ℤ) (r : ℤ)
    (m : N → ℤ) : afp_pair X c (r • m) = r * afp_pair X c m := by
  unfold afp_pair
  simp only [Pi.smul_apply, smul_eq_mul]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (∑ j, X i j * (r * m j)) = r * ∑ j, X i j * m j by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  ring

private lemma afp_pair_smul_left {N : Type} [Fintype N] (X : Matrix N N ℤ) (r : ℤ)
    (c m : N → ℤ) : afp_pair X (r • c) m = r * afp_pair X c m := by
  unfold afp_pair
  simp only [Pi.smul_apply, smul_eq_mul]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma afp_pair_single_left {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (k : N) (m : N → ℤ) : afp_pair X (Pi.single k 1) m = ∑ j, X k j * m j := by
  unfold afp_pair
  rw [Fintype.sum_eq_single k (fun i hi => by simp only [Pi.single_eq_of_ne hi, zero_mul])]
  simp only [Pi.single_eq_same, one_mul]

private lemma afp_pair_single_right {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (c : N → ℤ) (a : N) : afp_pair X c (Pi.single a 1) = ∑ i, c i * X i a := by
  unfold afp_pair
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Fintype.sum_eq_single a (fun j hj => by simp only [Pi.single_eq_of_ne hj, mul_zero])]
  simp only [Pi.single_eq_same, mul_one]

private lemma afp_pair_single_single {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (k : N) : afp_pair X (Pi.single k 1) (Pi.single k 1) = X k k := by
  rw [afp_pair_single_left]
  rw [Fintype.sum_eq_single k (fun j hj => by simp only [Pi.single_eq_of_ne hj, mul_zero])]
  simp only [Pi.single_eq_same, mul_one]

private lemma afp_pair_inv {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (j : N) (c m : N → ℤ) :
    afp_pair X (ggSReflR X j c) (ggSRefl X j m) = afp_pair X c m := by
  have hm : ggSRefl X j m = m - (∑ i, X j i * m i) • Pi.single j 1 := rfl
  have hc : ggSReflR X j c = c - (∑ i, c i * X i j) • Pi.single j 1 := rfl
  rw [hm, hc]
  rw [show m - (∑ i, X j i * m i) • Pi.single j 1
        = m + (-(∑ i, X j i * m i)) • Pi.single j 1 by rw [neg_smul, sub_eq_add_neg],
      show c - (∑ i, c i * X i j) • Pi.single j 1
        = c + (-(∑ i, c i * X i j)) • Pi.single j 1 by rw [neg_smul, sub_eq_add_neg]]
  rw [afp_pair_add, afp_pair_add_left, afp_pair_add_left]
  rw [afp_pair_smul_left, afp_pair_smul, afp_pair_smul, afp_pair_smul_left]
  rw [afp_pair_single_left, afp_pair_single_right, afp_pair_single_single, hX j]
  ring

private lemma afp_sRefl_self {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (hX : X j j = 2) : ggSRefl X j (Pi.single j 1) = - Pi.single j 1 := by
  rw [show ggSRefl X j (Pi.single j 1)
      = Pi.single j 1 - (∑ i, X j i * (Pi.single j 1 : N → ℤ) i) •
          (Pi.single j 1 : N → ℤ) from rfl]
  rw [show (∑ i, X j i * (Pi.single j 1 : N → ℤ) i) = X j j by
    rw [Fintype.sum_eq_single j (fun i hi => by simp only [Pi.single_eq_of_ne hi, mul_zero])]
    simp only [Pi.single_eq_same, mul_one]]
  rw [hX]
  module

private lemma afp_sRefl_sub_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (j : N) (m m' : N → ℤ) (r : ℤ) :
    ggSRefl X j (m - r • m') = ggSRefl X j m - r • ggSRefl X j m' := by
  funext i
  unfold ggSRefl
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ x, X j x * (m x - r * m' x))
      = (∑ x, X j x * m x) - r * ∑ x, X j x * m' x := by
    rw [show (∑ x, X j x * (m x - r * m' x))
          = ∑ x, (X j x * m x - r * (X j x * m' x)) by
      apply Finset.sum_congr rfl
      intro x _
      ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum]
  ring

private lemma afp_sRefl_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (r : ℤ) (m : N → ℤ) : ggSRefl X j (r • m) = r • ggSRefl X j m := by
  funext i
  unfold ggSRefl
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ x, X j x * (r * m x)) = r * ∑ x, X j x * m x by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  ring

private lemma afp_sRefl_invol {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (hX : X j j = 2) (m : N → ℤ) : ggSRefl X j (ggSRefl X j m) = m := by
  rw [show ggSRefl X j m = m - (∑ i, X j i * m i) • Pi.single j 1 from rfl]
  rw [afp_sRefl_sub_smul, afp_sRefl_self X j hX, smul_neg]
  rw [show ggSRefl X j m = m - (∑ i, X j i * m i) • Pi.single j 1 from rfl]
  abel

private lemma afp_sReflR_self {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (hX : X j j = 2) : ggSReflR X j (Pi.single j 1) = - Pi.single j 1 := by
  rw [show ggSReflR X j (Pi.single j 1)
      = Pi.single j 1 - (∑ i, (Pi.single j 1 : N → ℤ) i * X i j) •
          (Pi.single j 1 : N → ℤ) from rfl]
  rw [show (∑ i, (Pi.single j 1 : N → ℤ) i * X i j) = X j j by
    rw [Fintype.sum_eq_single j (fun i hi => by simp only [Pi.single_eq_of_ne hi, zero_mul])]
    simp only [Pi.single_eq_same, one_mul]]
  rw [hX]
  module

private lemma afp_sReflR_sub_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (j : N) (c c' : N → ℤ) (r : ℤ) :
    ggSReflR X j (c - r • c') = ggSReflR X j c - r • ggSReflR X j c' := by
  funext i
  unfold ggSReflR
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ x, (c x - r * c' x) * X x j)
      = (∑ x, c x * X x j) - r * ∑ x, c' x * X x j := by
    rw [show (∑ x, (c x - r * c' x) * X x j)
          = ∑ x, (c x * X x j - r * (c' x * X x j)) by
      apply Finset.sum_congr rfl
      intro x _
      ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum]
  ring

private lemma afp_sReflR_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (r : ℤ) (c : N → ℤ) : ggSReflR X j (r • c) = r • ggSReflR X j c := by
  funext i
  unfold ggSReflR
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ x, (r * c x) * X x j) = r * ∑ x, c x * X x j by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  ring

private lemma afp_sReflR_invol {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (hX : X j j = 2) (c : N → ℤ) : ggSReflR X j (ggSReflR X j c) = c := by
  rw [show ggSReflR X j c = c - (∑ i, c i * X i j) • Pi.single j 1 from rfl]
  rw [afp_sReflR_sub_smul, afp_sReflR_self X j hX, smul_neg]
  rw [show ggSReflR X j c = c - (∑ i, c i * X i j) • Pi.single j 1 from rfl]
  abel

private lemma afp_sWord_nil {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (m : N → ℤ) : ggSWord X [] m = m := rfl

private lemma afp_sWord_cons {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (ψ : List N) (m : N → ℤ) : ggSWord X (j :: ψ) m = ggSRefl X j (ggSWord X ψ m) := rfl

private lemma afp_sWordR_nil {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (c : N → ℤ) : ggSWordR X [] c = c := rfl

private lemma afp_sWordR_cons {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (ψ : List N) (c : N → ℤ) : ggSWordR X (j :: ψ) c = ggSReflR X j (ggSWordR X ψ c) := rfl

private lemma afp_sWord_append {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w₁ w₂ : List N) (m : N → ℤ) :
    ggSWord X (w₁ ++ w₂) m = ggSWord X w₁ (ggSWord X w₂ m) := by
  induction w₁ with
  | nil => rw [List.nil_append, afp_sWord_nil]
  | cons j w ih => rw [List.cons_append, afp_sWord_cons, ih, afp_sWord_cons]

private lemma afp_sWordR_append {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w₁ w₂ : List N) (c : N → ℤ) :
    ggSWordR X (w₁ ++ w₂) c = ggSWordR X w₁ (ggSWordR X w₂ c) := by
  induction w₁ with
  | nil => rw [List.nil_append, afp_sWordR_nil]
  | cons j w ih => rw [List.cons_append, afp_sWordR_cons, ih, afp_sWordR_cons]

private lemma afp_sWord_sub_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w : List N) (m m' : N → ℤ) (r : ℤ) :
    ggSWord X w (m - r • m') = ggSWord X w m - r • ggSWord X w m' := by
  induction w with
  | nil => rw [afp_sWord_nil, afp_sWord_nil, afp_sWord_nil]
  | cons j w ih => rw [afp_sWord_cons, afp_sWord_cons, afp_sWord_cons, ih, afp_sRefl_sub_smul]

private lemma afp_sWord_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w : List N) (r : ℤ) (m : N → ℤ) : ggSWord X w (r • m) = r • ggSWord X w m := by
  induction w with
  | nil => rw [afp_sWord_nil, afp_sWord_nil]
  | cons j w ih => rw [afp_sWord_cons, afp_sWord_cons, ih, afp_sRefl_smul]

private lemma afp_sWordR_sub_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w : List N) (c c' : N → ℤ) (r : ℤ) :
    ggSWordR X w (c - r • c') = ggSWordR X w c - r • ggSWordR X w c' := by
  induction w with
  | nil => rw [afp_sWordR_nil, afp_sWordR_nil, afp_sWordR_nil]
  | cons j w ih => rw [afp_sWordR_cons, afp_sWordR_cons, afp_sWordR_cons, ih, afp_sReflR_sub_smul]

private lemma afp_sWordR_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w : List N) (r : ℤ) (c : N → ℤ) : ggSWordR X w (r • c) = r • ggSWordR X w c := by
  induction w with
  | nil => rw [afp_sWordR_nil, afp_sWordR_nil]
  | cons j w ih => rw [afp_sWordR_cons, afp_sWordR_cons, ih, afp_sReflR_smul]

private lemma afp_pair_word_inv {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (ψ : List N) (m : N → ℤ) :
    afp_pair X (ggSWordR X ψ m) (ggSWord X ψ m) = afp_pair X m m := by
  induction ψ with
  | nil => rw [afp_sWordR_nil, afp_sWord_nil]
  | cons j ψ ih => rw [afp_sWordR_cons, afp_sWord_cons, afp_pair_inv X hX j, ih]

private lemma afp_sWord_conj {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (ψ : List N) (k : N) (m : N → ℤ) :
    ggSWord X (ψ ++ [k] ++ ψ.reverse) m =
      m - (afp_pair X (ggSWordR X ψ (Pi.single k 1)) m) • ggSWord X ψ (Pi.single k 1) := by
  induction ψ generalizing m with
  | nil =>
    simp only [List.nil_append, List.reverse_nil, List.append_nil, afp_sWord_cons, afp_sWord_nil,
      afp_sWordR_nil, afp_pair_single_left]
    rfl
  | cons j ψ ih =>
    have hsplit : ggSWord X (ψ ++ [k] ++ ψ.reverse ++ [j]) m
        = ggSWord X (ψ ++ [k] ++ ψ.reverse) (ggSRefl X j m) := by
      rw [show ψ ++ [k] ++ ψ.reverse ++ [j] = (ψ ++ [k] ++ ψ.reverse) ++ [j] by
        simp only [List.append_assoc]]
      rw [afp_sWord_append, afp_sWord_cons, afp_sWord_nil]
    have hword : (j :: ψ) ++ [k] ++ (j :: ψ).reverse
        = j :: (ψ ++ [k] ++ ψ.reverse ++ [j]) := by
      simp only [List.reverse_cons, List.append_assoc, List.cons_append]
    rw [hword]
    simp only [afp_sWord_cons, afp_sWordR_cons]
    rw [hsplit, ih]
    rw [afp_sRefl_sub_smul, afp_sRefl_invol X j (hX j)]
    have hp : afp_pair X (ggSWordR X ψ (Pi.single k 1)) (ggSRefl X j m)
        = afp_pair X (ggSReflR X j (ggSWordR X ψ (Pi.single k 1))) m := by
      have h := afp_pair_inv X hX j (ggSReflR X j (ggSWordR X ψ (Pi.single k 1))) m
      rwa [afp_sReflR_invol X j (hX j) (ggSWordR X ψ (Pi.single k 1))] at h
    rw [hp]

private lemma afp_sWordR_conj {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (ψ : List N) (k : N) (c : N → ℤ) :
    ggSWordR X (ψ ++ [k] ++ ψ.reverse) c =
      c - (afp_pair X c (ggSWord X ψ (Pi.single k 1))) • ggSWordR X ψ (Pi.single k 1) := by
  induction ψ generalizing c with
  | nil =>
    simp only [List.nil_append, List.reverse_nil, List.append_nil, afp_sWordR_cons, afp_sWordR_nil,
      afp_sWord_nil, afp_pair_single_right]
    rfl
  | cons j ψ ih =>
    have hsplit : ggSWordR X (ψ ++ [k] ++ ψ.reverse ++ [j]) c
        = ggSWordR X (ψ ++ [k] ++ ψ.reverse) (ggSReflR X j c) := by
      rw [show ψ ++ [k] ++ ψ.reverse ++ [j] = (ψ ++ [k] ++ ψ.reverse) ++ [j] by
        simp only [List.append_assoc]]
      rw [afp_sWordR_append, afp_sWordR_cons, afp_sWordR_nil]
    have hword : (j :: ψ) ++ [k] ++ (j :: ψ).reverse
        = j :: (ψ ++ [k] ++ ψ.reverse ++ [j]) := by
      simp only [List.reverse_cons, List.append_assoc, List.cons_append]
    rw [hword]
    simp only [afp_sWord_cons, afp_sWordR_cons]
    rw [hsplit, ih]
    rw [afp_sReflR_sub_smul, afp_sReflR_invol X j (hX j)]
    have hp : afp_pair X (ggSReflR X j c) (ggSWord X ψ (Pi.single k 1))
        = afp_pair X c (ggSRefl X j (ggSWord X ψ (Pi.single k 1))) := by
      have h := afp_pair_inv X hX j c (ggSRefl X j (ggSWord X ψ (Pi.single k 1)))
      rwa [afp_sRefl_invol X j (hX j) (ggSWord X ψ (Pi.single k 1))] at h
    rw [hp]

private lemma afp_row_delta {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (a : N)
    (G : N → ℤ) (hXa : X a a = 2) (h : (∑ j, X a j * G j) = -2) :
    (∑ i, X a i * ((Pi.single a 1 : N → ℤ) + G) i) = 0 := by
  rw [show (∑ i, X a i * ((Pi.single a 1 : N → ℤ) + G) i)
        = (∑ i, X a i * (Pi.single a 1 : N → ℤ) i) + ∑ i, X a i * G i by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Pi.add_apply, mul_add]]
  rw [show (∑ i, X a i * (Pi.single a 1 : N → ℤ) i) = X a a by
    rw [Fintype.sum_eq_single a (fun i hi => by simp only [Pi.single_eq_of_ne hi, mul_zero])]
    simp only [Pi.single_eq_same, mul_one]]
  rw [hXa, h]
  norm_num

private lemma afp_col_delta {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (a : N)
    (G : N → ℤ) (hXa : X a a = 2) (h : (∑ i, G i * X i a) = -2) :
    (∑ i, ((Pi.single a 1 : N → ℤ) + G) i * X i a) = 0 := by
  rw [show (∑ i, ((Pi.single a 1 : N → ℤ) + G) i * X i a)
        = (∑ i, (Pi.single a 1 : N → ℤ) i * X i a) + ∑ i, G i * X i a by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Pi.add_apply, add_mul]]
  rw [show (∑ i, (Pi.single a 1 : N → ℤ) i * X i a) = X a a by
    rw [Fintype.sum_eq_single a (fun i hi => by simp only [Pi.single_eq_of_ne hi, zero_mul])]
    simp only [Pi.single_eq_same, one_mul]]
  rw [hXa, h]
  norm_num

private lemma afp_sRefl_fix {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (m : N → ℤ) (h : (∑ i, X j i * m i) = 0) : ggSRefl X j m = m := by
  unfold ggSRefl
  rw [h, zero_smul, sub_zero]

private lemma afp_sReflR_fix {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (c : N → ℤ) (h : (∑ i, c i * X i j) = 0) : ggSReflR X j c = c := by
  unfold ggSReflR
  rw [h, zero_smul, sub_zero]

private lemma afp_affineWord_zero {N : Type} (ψγ : List N) (kγ a : N) :
    ggAffineWord ψγ kγ a 0 = [] := rfl

private lemma afp_affineWord_succ {N : Type} (ψγ : List N) (kγ a : N) (m : ℕ) :
    ggAffineWord ψγ kγ a (m + 1)
      = (ψγ ++ [kγ] ++ ψγ.reverse ++ [a]) ++ ggAffineWord ψγ kγ a m := by
  unfold ggAffineWord
  rw [List.replicate_succ, List.flatten_cons]

private lemma afp_sWord_affine {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (a kγ : N) (ψγ : List N)
    (hp1 : afp_pair X (Pi.single a 1) (ggSWord X ψγ (Pi.single kγ 1)) = -2)
    (hp2 : afp_pair X (ggSWordR X ψγ (Pi.single kγ 1)) (Pi.single a 1) = -2) (m : ℕ) :
    ggSWord X (ggAffineWord ψγ kγ a m) (Pi.single a 1) =
      Pi.single a 1 - (2 * (m : ℤ)) • (Pi.single a 1 + ggSWord X ψγ (Pi.single kγ 1)) := by
  have hp1' : (∑ j, X a j * ggSWord X ψγ (Pi.single kγ 1) j) = -2 := by
    rw [← afp_pair_single_left X a (ggSWord X ψγ (Pi.single kγ 1))]
    exact hp1
  have hfix : ggSRefl X a (Pi.single a 1 + ggSWord X ψγ (Pi.single kγ 1)) =
      Pi.single a 1 + ggSWord X ψγ (Pi.single kγ 1) :=
    afp_sRefl_fix X a _ (afp_row_delta X a _ (hX a) hp1')
  have hpair : afp_pair X (ggSWordR X ψγ (Pi.single kγ 1))
      (ggSWord X ψγ (Pi.single kγ 1)) = 2 := by
    rw [afp_pair_word_inv X hX ψγ (Pi.single kγ 1), afp_pair_single_single, hX kγ]
  have hTa : ggSRefl X a (Pi.single a 1) = - Pi.single a 1 := afp_sRefl_self X a (hX a)
  have hWe : ggSWord X (ψγ ++ [kγ] ++ ψγ.reverse) (Pi.single a 1) =
      Pi.single a 1 + (2 : ℤ) • ggSWord X ψγ (Pi.single kγ 1) := by
    rw [afp_sWord_conj X hX ψγ kγ (Pi.single a 1), hp2]
    module
  have hWneg : ggSWord X (ψγ ++ [kγ] ++ ψγ.reverse) (- Pi.single a 1) =
      - ggSWord X (ψγ ++ [kγ] ++ ψγ.reverse) (Pi.single a 1) := by
    rw [show (- Pi.single a 1 : N → ℤ) = (-1 : ℤ) • Pi.single a 1 by rw [neg_one_smul],
      afp_sWord_smul, neg_one_smul]
  have hWT : ψγ ++ [kγ] ++ ψγ.reverse ++ [a] = (ψγ ++ [kγ] ++ ψγ.reverse) ++ [a] := by
    simp only [List.append_assoc]
  have hTe : ggSWord X (ψγ ++ [kγ] ++ ψγ.reverse ++ [a]) (Pi.single a 1) =
      Pi.single a 1 - (2 : ℤ) • (Pi.single a 1 + ggSWord X ψγ (Pi.single kγ 1)) := by
    rw [hWT, afp_sWord_append, afp_sWord_cons, afp_sWord_nil, hTa, hWneg, hWe]
    module
  have hTfix : ggSWord X (ψγ ++ [kγ] ++ ψγ.reverse ++ [a])
      (Pi.single a 1 + ggSWord X ψγ (Pi.single kγ 1)) =
      Pi.single a 1 + ggSWord X ψγ (Pi.single kγ 1) := by
    rw [hWT, afp_sWord_append, afp_sWord_cons, afp_sWord_nil, hfix]
    rw [afp_sWord_conj X hX ψγ kγ (Pi.single a 1 + ggSWord X ψγ (Pi.single kγ 1)),
      afp_pair_add, hp2, hpair]
    module
  induction m with
  | zero =>
    rw [afp_affineWord_zero, afp_sWord_nil]
    simp
  | succ m ih =>
    rw [afp_affineWord_succ, afp_sWord_append, ih, afp_sWord_sub_smul, hTe, hTfix]
    push_cast
    module

private lemma afp_sWordR_affine {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (a kγ : N) (ψγ : List N)
    (hp1 : afp_pair X (Pi.single a 1) (ggSWord X ψγ (Pi.single kγ 1)) = -2)
    (hp2 : afp_pair X (ggSWordR X ψγ (Pi.single kγ 1)) (Pi.single a 1) = -2) (m : ℕ) :
    ggSWordR X (ggAffineWord ψγ kγ a m) (Pi.single a 1) =
      Pi.single a 1 - (2 * (m : ℤ)) • (Pi.single a 1 + ggSWordR X ψγ (Pi.single kγ 1)) := by
  have hp2' : (∑ i, ggSWordR X ψγ (Pi.single kγ 1) i * X i a) = -2 := by
    rw [← afp_pair_single_right X (ggSWordR X ψγ (Pi.single kγ 1)) a]
    exact hp2
  have hpair : afp_pair X (ggSWordR X ψγ (Pi.single kγ 1))
      (ggSWord X ψγ (Pi.single kγ 1)) = 2 := by
    rw [afp_pair_word_inv X hX ψγ (Pi.single kγ 1), afp_pair_single_single, hX kγ]
  have hfixR : ggSReflR X a (Pi.single a 1 + ggSWordR X ψγ (Pi.single kγ 1)) =
      Pi.single a 1 + ggSWordR X ψγ (Pi.single kγ 1) :=
    afp_sReflR_fix X a _ (afp_col_delta X a _ (hX a) hp2')
  have hTaR : ggSReflR X a (Pi.single a 1) = - Pi.single a 1 := afp_sReflR_self X a (hX a)
  have hWeR : ggSWordR X (ψγ ++ [kγ] ++ ψγ.reverse) (Pi.single a 1) =
      Pi.single a 1 + (2 : ℤ) • ggSWordR X ψγ (Pi.single kγ 1) := by
    rw [afp_sWordR_conj X hX ψγ kγ (Pi.single a 1), hp1]
    module
  have hWnegR : ggSWordR X (ψγ ++ [kγ] ++ ψγ.reverse) (- Pi.single a 1) =
      - ggSWordR X (ψγ ++ [kγ] ++ ψγ.reverse) (Pi.single a 1) := by
    rw [show (- Pi.single a 1 : N → ℤ) = (-1 : ℤ) • Pi.single a 1 by rw [neg_one_smul],
      afp_sWordR_smul, neg_one_smul]
  have hWT : ψγ ++ [kγ] ++ ψγ.reverse ++ [a] = (ψγ ++ [kγ] ++ ψγ.reverse) ++ [a] := by
    simp only [List.append_assoc]
  have hTeR : ggSWordR X (ψγ ++ [kγ] ++ ψγ.reverse ++ [a]) (Pi.single a 1) =
      Pi.single a 1 - (2 : ℤ) • (Pi.single a 1 + ggSWordR X ψγ (Pi.single kγ 1)) := by
    rw [hWT, afp_sWordR_append, afp_sWordR_cons, afp_sWordR_nil, hTaR, hWnegR, hWeR]
    module
  have hTfixR : ggSWordR X (ψγ ++ [kγ] ++ ψγ.reverse ++ [a])
      (Pi.single a 1 + ggSWordR X ψγ (Pi.single kγ 1)) =
      Pi.single a 1 + ggSWordR X ψγ (Pi.single kγ 1) := by
    rw [hWT, afp_sWordR_append, afp_sWordR_cons, afp_sWordR_nil, hfixR]
    rw [afp_sWordR_conj X hX ψγ kγ (Pi.single a 1 + ggSWordR X ψγ (Pi.single kγ 1)),
      afp_pair_add_left, hp1, hpair]
    module
  induction m with
  | zero =>
    rw [afp_affineWord_zero, afp_sWordR_nil]
    simp
  | succ m ih =>
    rw [afp_affineWord_succ, afp_sWordR_append, ih, afp_sWordR_sub_smul, hTeR, hTfixR]
    push_cast
    module

theorem ggAffinePair_word {N : Type} [Fintype N] [DecidableEq N]
    (X : Matrix N N ℤ) (hX : ∀ j, X j j = 2) (a kγ : N) (ψγ : List N)
    (hP1 : ∑ j, ggSWord X ψγ (Pi.single kγ 1) j * X a j = -2)
    (hP2 : ∑ i, ggSWordR X ψγ (Pi.single kγ 1) i * X i a = -2) (m : ℕ) :
    ggSWord X (ggAffineWord ψγ kγ a m) (Pi.single a 1) =
        Pi.single a 1 - (2 * (m : ℤ)) • (Pi.single a 1 + ggSWord X ψγ (Pi.single kγ 1)) ∧
      ggSWordR X (ggAffineWord ψγ kγ a m) (Pi.single a 1) =
        Pi.single a 1 - (2 * (m : ℤ)) • (Pi.single a 1 + ggSWordR X ψγ (Pi.single kγ 1)) := by
  have hp1 : afp_pair X (Pi.single a 1) (ggSWord X ψγ (Pi.single kγ 1)) = -2 := by
    rw [afp_pair_single_left]
    calc ∑ j, X a j * ggSWord X ψγ (Pi.single kγ 1) j
        = ∑ j, ggSWord X ψγ (Pi.single kγ 1) j * X a j := by
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = -2 := hP1
  have hp2 : afp_pair X (ggSWordR X ψγ (Pi.single kγ 1)) (Pi.single a 1) = -2 := by
    rw [afp_pair_single_right]
    exact hP2
  exact ⟨afp_sWord_affine X hX a kγ ψγ hp1 hp2 m,
    afp_sWordR_affine X hX a kγ ψγ hp1 hp2 m⟩

end Lattice

end CFSG.StandardType
