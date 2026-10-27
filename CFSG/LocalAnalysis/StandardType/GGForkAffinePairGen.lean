module

public import CFSG.LocalAnalysis.StandardType.GGForkAffinePair

public section

namespace CFSG.StandardType

private def apg_pair {N : Type} [Fintype N] (X : Matrix N N ℤ) (c m : N → ℤ) : ℤ :=
  ∑ i, c i * ∑ j, X i j * m j

private lemma apg_pair_add {N : Type} [Fintype N] (X : Matrix N N ℤ) (c m m' : N → ℤ) :
    apg_pair X c (m + m') = apg_pair X c m + apg_pair X c m' := by
  simp only [apg_pair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma apg_pair_add_left {N : Type} [Fintype N] (X : Matrix N N ℤ) (c c' m : N → ℤ) :
    apg_pair X (c + c') m = apg_pair X c m + apg_pair X c' m := by
  simp only [apg_pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma apg_pair_smul {N : Type} [Fintype N] (X : Matrix N N ℤ) (c : N → ℤ) (r : ℤ)
    (m : N → ℤ) : apg_pair X c (r • m) = r * apg_pair X c m := by
  unfold apg_pair
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

private lemma apg_pair_smul_left {N : Type} [Fintype N] (X : Matrix N N ℤ) (r : ℤ)
    (c m : N → ℤ) : apg_pair X (r • c) m = r * apg_pair X c m := by
  unfold apg_pair
  simp only [Pi.smul_apply, smul_eq_mul]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma apg_pair_single_left {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (k : N) (m : N → ℤ) : apg_pair X (Pi.single k 1) m = ∑ j, X k j * m j := by
  unfold apg_pair
  rw [Fintype.sum_eq_single k (fun i hi => by simp only [Pi.single_eq_of_ne hi, zero_mul])]
  simp only [Pi.single_eq_same, one_mul]

private lemma apg_pair_single_right {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (c : N → ℤ) (a : N) : apg_pair X c (Pi.single a 1) = ∑ i, c i * X i a := by
  unfold apg_pair
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Fintype.sum_eq_single a (fun j hj => by simp only [Pi.single_eq_of_ne hj, mul_zero])]
  simp only [Pi.single_eq_same, mul_one]

private lemma apg_pair_single_single {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (k : N) : apg_pair X (Pi.single k 1) (Pi.single k 1) = X k k := by
  rw [apg_pair_single_left]
  rw [Fintype.sum_eq_single k (fun j hj => by simp only [Pi.single_eq_of_ne hj, mul_zero])]
  simp only [Pi.single_eq_same, mul_one]

private lemma apg_pair_inv {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (j : N) (c m : N → ℤ) :
    apg_pair X (ggSReflR X j c) (ggSRefl X j m) = apg_pair X c m := by
  have hm : ggSRefl X j m = m - (∑ i, X j i * m i) • Pi.single j 1 := rfl
  have hc : ggSReflR X j c = c - (∑ i, c i * X i j) • Pi.single j 1 := rfl
  rw [hm, hc]
  rw [show m - (∑ i, X j i * m i) • Pi.single j 1
        = m + (-(∑ i, X j i * m i)) • Pi.single j 1 by rw [neg_smul, sub_eq_add_neg],
      show c - (∑ i, c i * X i j) • Pi.single j 1
        = c + (-(∑ i, c i * X i j)) • Pi.single j 1 by rw [neg_smul, sub_eq_add_neg]]
  rw [apg_pair_add, apg_pair_add_left, apg_pair_add_left]
  rw [apg_pair_smul_left, apg_pair_smul, apg_pair_smul, apg_pair_smul_left]
  rw [apg_pair_single_left, apg_pair_single_right, apg_pair_single_single, hX j]
  ring

private lemma apg_sWord_nil {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (m : N → ℤ) : ggSWord X [] m = m := rfl

private lemma apg_sWord_cons {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (ψ : List N) (m : N → ℤ) : ggSWord X (j :: ψ) m = ggSRefl X j (ggSWord X ψ m) := rfl

private lemma apg_sWordR_nil {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (c : N → ℤ) : ggSWordR X [] c = c := rfl

private lemma apg_sWordR_cons {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (ψ : List N) (c : N → ℤ) : ggSWordR X (j :: ψ) c = ggSReflR X j (ggSWordR X ψ c) := rfl

private lemma apg_pair_word_inv {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (ψ : List N) (c m : N → ℤ) :
    apg_pair X (ggSWordR X ψ c) (ggSWord X ψ m) = apg_pair X c m := by
  induction ψ generalizing c m with
  | nil => rw [apg_sWordR_nil, apg_sWord_nil]
  | cons j ψ ih =>
    rw [apg_sWordR_cons, apg_sWord_cons, apg_pair_inv X hX j, ih]

private lemma apg_sRefl_self {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (hX : X j j = 2) : ggSRefl X j (Pi.single j 1) = - Pi.single j 1 := by
  rw [show ggSRefl X j (Pi.single j 1)
      = Pi.single j 1 - (∑ i, X j i * (Pi.single j 1 : N → ℤ) i) •
          (Pi.single j 1 : N → ℤ) from rfl]
  rw [show (∑ i, X j i * (Pi.single j 1 : N → ℤ) i) = X j j by
    rw [Fintype.sum_eq_single j (fun i hi => by simp only [Pi.single_eq_of_ne hi, mul_zero])]
    simp only [Pi.single_eq_same, mul_one]]
  rw [hX]
  module

private lemma apg_sRefl_sub_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
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

private lemma apg_sRefl_add {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (m m' : N → ℤ) : ggSRefl X j (m + m') = ggSRefl X j m + ggSRefl X j m' := by
  funext i
  unfold ggSRefl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ x, X j x * (m x + m' x))
      = (∑ x, X j x * m x) + ∑ x, X j x * m' x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  ring

private lemma apg_sRefl_invol {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (hX : X j j = 2) (m : N → ℤ) : ggSRefl X j (ggSRefl X j m) = m := by
  rw [show ggSRefl X j m = m - (∑ i, X j i * m i) • Pi.single j 1 from rfl]
  rw [apg_sRefl_sub_smul, apg_sRefl_self X j hX, smul_neg]
  rw [show ggSRefl X j m = m - (∑ i, X j i * m i) • Pi.single j 1 from rfl]
  abel

private lemma apg_sReflR_self {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (hX : X j j = 2) : ggSReflR X j (Pi.single j 1) = - Pi.single j 1 := by
  rw [show ggSReflR X j (Pi.single j 1)
      = Pi.single j 1 - (∑ i, (Pi.single j 1 : N → ℤ) i * X i j) •
          (Pi.single j 1 : N → ℤ) from rfl]
  rw [show (∑ i, (Pi.single j 1 : N → ℤ) i * X i j) = X j j by
    rw [Fintype.sum_eq_single j (fun i hi => by simp only [Pi.single_eq_of_ne hi, zero_mul])]
    simp only [Pi.single_eq_same, one_mul]]
  rw [hX]
  module

private lemma apg_sReflR_sub_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
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

private lemma apg_sReflR_add {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (c c' : N → ℤ) : ggSReflR X j (c + c') = ggSReflR X j c + ggSReflR X j c' := by
  funext i
  unfold ggSReflR
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ x, (c x + c' x) * X x j)
      = (∑ x, c x * X x j) + ∑ x, c' x * X x j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  ring

private lemma apg_sReflR_invol {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (hX : X j j = 2) (c : N → ℤ) : ggSReflR X j (ggSReflR X j c) = c := by
  rw [show ggSReflR X j c = c - (∑ i, c i * X i j) • Pi.single j 1 from rfl]
  rw [apg_sReflR_sub_smul, apg_sReflR_self X j hX, smul_neg]
  rw [show ggSReflR X j c = c - (∑ i, c i * X i j) • Pi.single j 1 from rfl]
  abel

private lemma apg_sWord_append {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w₁ w₂ : List N) (m : N → ℤ) :
    ggSWord X (w₁ ++ w₂) m = ggSWord X w₁ (ggSWord X w₂ m) := by
  induction w₁ with
  | nil => rw [List.nil_append, apg_sWord_nil]
  | cons j w ih => rw [List.cons_append, apg_sWord_cons, ih, apg_sWord_cons]

private lemma apg_sWordR_append {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w₁ w₂ : List N) (c : N → ℤ) :
    ggSWordR X (w₁ ++ w₂) c = ggSWordR X w₁ (ggSWordR X w₂ c) := by
  induction w₁ with
  | nil => rw [List.nil_append, apg_sWordR_nil]
  | cons j w ih => rw [List.cons_append, apg_sWordR_cons, ih, apg_sWordR_cons]

private lemma apg_sWord_append_reverse {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (l : List N) (m : N → ℤ) : ggSWord X (l ++ l.reverse) m = m := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, List.cons_append, ← List.append_assoc, apg_sWord_cons,
      apg_sWord_append, ih, apg_sWord_cons, apg_sWord_nil, apg_sRefl_invol X a (hX a)]

private lemma apg_sWord_reverse_append {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (l : List N) (m : N → ℤ) : ggSWord X (l.reverse ++ l) m = m := by
  have h := apg_sWord_append_reverse X hX l.reverse m
  rwa [List.reverse_reverse] at h

private lemma apg_sWordR_append_reverse {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (l : List N) (c : N → ℤ) : ggSWordR X (l ++ l.reverse) c = c := by
  induction l generalizing c with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, List.cons_append, ← List.append_assoc, apg_sWordR_cons,
      apg_sWordR_append, ih, apg_sWordR_cons, apg_sWordR_nil, apg_sReflR_invol X a (hX a)]

private lemma apg_sWordR_reverse_append {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (l : List N) (c : N → ℤ) : ggSWordR X (l.reverse ++ l) c = c := by
  have h := apg_sWordR_append_reverse X hX l.reverse c
  rwa [List.reverse_reverse] at h

private lemma apg_sWord_sub_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w : List N) (m m' : N → ℤ) (r : ℤ) :
    ggSWord X w (m - r • m') = ggSWord X w m - r • ggSWord X w m' := by
  induction w with
  | nil => rw [apg_sWord_nil, apg_sWord_nil, apg_sWord_nil]
  | cons j w ih => rw [apg_sWord_cons, apg_sWord_cons, apg_sWord_cons, ih, apg_sRefl_sub_smul]

private lemma apg_sWordR_sub_smul {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w : List N) (c c' : N → ℤ) (r : ℤ) :
    ggSWordR X w (c - r • c') = ggSWordR X w c - r • ggSWordR X w c' := by
  induction w with
  | nil => rw [apg_sWordR_nil, apg_sWordR_nil, apg_sWordR_nil]
  | cons j w ih => rw [apg_sWordR_cons, apg_sWordR_cons, apg_sWordR_cons, ih, apg_sReflR_sub_smul]

private lemma apg_sWord_add {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w : List N) (m m' : N → ℤ) : ggSWord X w (m + m') = ggSWord X w m + ggSWord X w m' := by
  induction w with
  | nil => rw [apg_sWord_nil, apg_sWord_nil, apg_sWord_nil]
  | cons j w ih => rw [apg_sWord_cons, apg_sWord_cons, apg_sWord_cons, ih, apg_sRefl_add]

private lemma apg_sWordR_add {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (w : List N) (c c' : N → ℤ) : ggSWordR X w (c + c') = ggSWordR X w c + ggSWordR X w c' := by
  induction w with
  | nil => rw [apg_sWordR_nil, apg_sWordR_nil, apg_sWordR_nil]
  | cons j w ih => rw [apg_sWordR_cons, apg_sWordR_cons, apg_sWordR_cons, ih, apg_sReflR_add]

private lemma apg_sWord_gen_word {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (k₀ kγ : N) (ψ₀ ψγ : List N) (m : ℕ) (v : N → ℤ) :
    ggSWord X ((List.replicate m (ψγ ++ [kγ] ++ ψγ.reverse ++ ψ₀ ++ [k₀] ++ ψ₀.reverse)).flatten
        ++ ψ₀) v
      = ggSWord X (ψ₀ ++ (List.replicate m
          ((ψ₀.reverse ++ ψγ) ++ [kγ] ++ (ψ₀.reverse ++ ψγ).reverse ++ [k₀])).flatten) v := by
  let T : List N := ψγ ++ [kγ] ++ ψγ.reverse ++ ψ₀ ++ [k₀] ++ ψ₀.reverse
  let T' : List N := (ψ₀.reverse ++ ψγ) ++ [kγ] ++ (ψ₀.reverse ++ ψγ).reverse ++ [k₀]
  let A : List N := ψγ ++ [kγ] ++ ψγ.reverse ++ ψ₀ ++ [k₀]
  have hT : T = A ++ ψ₀.reverse := by
    simp only [T, A, List.append_assoc]
  have hT' : T' = ψ₀.reverse ++ A := by
    simp only [T', A, List.reverse_append, List.reverse_reverse, List.append_assoc]
  have hTψ : T ++ ψ₀ = A ++ (ψ₀.reverse ++ ψ₀) := by rw [hT, List.append_assoc]
  have hψT' : ψ₀ ++ T' = (ψ₀ ++ ψ₀.reverse) ++ A := by rw [hT', ← List.append_assoc]
  have hbase : ∀ w : N → ℤ, ggSWord X (T ++ ψ₀) w = ggSWord X (ψ₀ ++ T') w := by
    intro w
    rw [hTψ, hψT']
    conv_lhs => rw [apg_sWord_append]
    conv_rhs => rw [apg_sWord_append]
    conv_lhs => rw [apg_sWord_reverse_append X hX ψ₀ w]
    conv_rhs => rw [apg_sWord_append_reverse X hX ψ₀ (ggSWord X A w)]
  have hmain : ggSWord X ((List.replicate m T).flatten ++ ψ₀) v
      = ggSWord X (ψ₀ ++ (List.replicate m T').flatten) v := by
    induction m with
    | zero => simp only [List.replicate_zero, List.flatten_nil, List.nil_append, List.append_nil]
    | succ m ih =>
      calc
        ggSWord X ((List.replicate (m + 1) T).flatten ++ ψ₀) v
            = ggSWord X (T ++ ((List.replicate m T).flatten ++ ψ₀)) v := by
                rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
          _ = ggSWord X T (ggSWord X ((List.replicate m T).flatten ++ ψ₀) v) := by
                rw [apg_sWord_append]
          _ = ggSWord X T (ggSWord X (ψ₀ ++ (List.replicate m T').flatten) v) := by
                rw [ih]
          _ = ggSWord X (T ++ ψ₀) (ggSWord X (List.replicate m T').flatten v) := by
                conv_lhs => rw [← apg_sWord_append]
                conv_rhs => rw [← apg_sWord_append]
                rw [← List.append_assoc]
          _ = ggSWord X (ψ₀ ++ T') (ggSWord X (List.replicate m T').flatten v) := by
                rw [hbase]
          _ = ggSWord X ψ₀ (ggSWord X T' (ggSWord X (List.replicate m T').flatten v)) := by
                rw [apg_sWord_append]
          _ = ggSWord X (ψ₀ ++ (List.replicate (m + 1) T').flatten) v := by
                rw [List.replicate_succ, List.flatten_cons, ← apg_sWord_append, ← apg_sWord_append,
                  List.append_assoc]
  exact hmain

private lemma apg_sWordR_gen_word {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ)
    (hX : ∀ j, X j j = 2) (k₀ kγ : N) (ψ₀ ψγ : List N) (m : ℕ) (v : N → ℤ) :
    ggSWordR X ((List.replicate m (ψγ ++ [kγ] ++ ψγ.reverse ++ ψ₀ ++ [k₀] ++ ψ₀.reverse)).flatten
        ++ ψ₀) v
      = ggSWordR X (ψ₀ ++ (List.replicate m
          ((ψ₀.reverse ++ ψγ) ++ [kγ] ++ (ψ₀.reverse ++ ψγ).reverse ++ [k₀])).flatten) v := by
  let T : List N := ψγ ++ [kγ] ++ ψγ.reverse ++ ψ₀ ++ [k₀] ++ ψ₀.reverse
  let T' : List N := (ψ₀.reverse ++ ψγ) ++ [kγ] ++ (ψ₀.reverse ++ ψγ).reverse ++ [k₀]
  let A : List N := ψγ ++ [kγ] ++ ψγ.reverse ++ ψ₀ ++ [k₀]
  have hT : T = A ++ ψ₀.reverse := by
    simp only [T, A, List.append_assoc]
  have hT' : T' = ψ₀.reverse ++ A := by
    simp only [T', A, List.reverse_append, List.reverse_reverse, List.append_assoc]
  have hTψ : T ++ ψ₀ = A ++ (ψ₀.reverse ++ ψ₀) := by rw [hT, List.append_assoc]
  have hψT' : ψ₀ ++ T' = (ψ₀ ++ ψ₀.reverse) ++ A := by rw [hT', ← List.append_assoc]
  have hbase : ∀ w : N → ℤ, ggSWordR X (T ++ ψ₀) w = ggSWordR X (ψ₀ ++ T') w := by
    intro w
    rw [hTψ, hψT']
    conv_lhs => rw [apg_sWordR_append]
    conv_rhs => rw [apg_sWordR_append]
    conv_lhs => rw [apg_sWordR_reverse_append X hX ψ₀ w]
    conv_rhs => rw [apg_sWordR_append_reverse X hX ψ₀ (ggSWordR X A w)]
  have hmain : ggSWordR X ((List.replicate m T).flatten ++ ψ₀) v
      = ggSWordR X (ψ₀ ++ (List.replicate m T').flatten) v := by
    induction m with
    | zero => simp only [List.replicate_zero, List.flatten_nil, List.nil_append, List.append_nil]
    | succ m ih =>
      calc
        ggSWordR X ((List.replicate (m + 1) T).flatten ++ ψ₀) v
            = ggSWordR X (T ++ ((List.replicate m T).flatten ++ ψ₀)) v := by
                rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
          _ = ggSWordR X T (ggSWordR X ((List.replicate m T).flatten ++ ψ₀) v) := by
                rw [apg_sWordR_append]
          _ = ggSWordR X T (ggSWordR X (ψ₀ ++ (List.replicate m T').flatten) v) := by
                rw [ih]
          _ = ggSWordR X (T ++ ψ₀) (ggSWordR X (List.replicate m T').flatten v) := by
                conv_lhs => rw [← apg_sWordR_append]
                conv_rhs => rw [← apg_sWordR_append]
                rw [← List.append_assoc]
          _ = ggSWordR X (ψ₀ ++ T') (ggSWordR X (List.replicate m T').flatten v) := by
                rw [hbase]
          _ = ggSWordR X ψ₀ (ggSWordR X T' (ggSWordR X (List.replicate m T').flatten v)) := by
                rw [apg_sWordR_append]
          _ = ggSWordR X (ψ₀ ++ (List.replicate (m + 1) T').flatten) v := by
                rw [List.replicate_succ, List.flatten_cons, ← apg_sWordR_append,
                  ← apg_sWordR_append, List.append_assoc]
  exact hmain

theorem ggAffinePair_word_gen {N : Type} [Fintype N] [DecidableEq N]
    (X : Matrix N N ℤ) (hX : ∀ j, X j j = 2) (k₀ kγ : N) (ψ₀ ψγ : List N)
    (hP1 : ∑ i, ∑ j, ggSWordR X ψ₀ (Pi.single k₀ 1) i * X i j *
      ggSWord X ψγ (Pi.single kγ 1) j = -2)
    (hP2 : ∑ i, ∑ j, ggSWordR X ψγ (Pi.single kγ 1) i * X i j *
      ggSWord X ψ₀ (Pi.single k₀ 1) j = -2) (m : ℕ) :
    ggSWord X ((List.replicate m (ψγ ++ [kγ] ++ ψγ.reverse ++ ψ₀ ++ [k₀] ++ ψ₀.reverse)).flatten ++
        ψ₀) (Pi.single k₀ 1) =
        ggSWord X ψ₀ (Pi.single k₀ 1) -
          (2 * (m : ℤ)) • (ggSWord X ψ₀ (Pi.single k₀ 1) + ggSWord X ψγ (Pi.single kγ 1)) ∧
      ggSWordR X ((List.replicate m (ψγ ++ [kγ] ++ ψγ.reverse ++ ψ₀ ++ [k₀] ++
        ψ₀.reverse)).flatten ++ ψ₀) (Pi.single k₀ 1) =
        ggSWordR X ψ₀ (Pi.single k₀ 1) -
          (2 * (m : ℤ)) • (ggSWordR X ψ₀ (Pi.single k₀ 1) + ggSWordR X ψγ (Pi.single kγ 1)) := by
  have hP1' : apg_pair X (ggSWordR X ψ₀ (Pi.single k₀ 1))
      (ggSWord X ψγ (Pi.single kγ 1)) = -2 := by
    unfold apg_pair
    rw [show (∑ i, ggSWordR X ψ₀ (Pi.single k₀ 1) i *
            ∑ j, X i j * ggSWord X ψγ (Pi.single kγ 1) j)
          = ∑ i, ∑ j, ggSWordR X ψ₀ (Pi.single k₀ 1) i * X i j *
              ggSWord X ψγ (Pi.single kγ 1) j by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    exact hP1
  have hP2' : apg_pair X (ggSWordR X ψγ (Pi.single kγ 1))
      (ggSWord X ψ₀ (Pi.single k₀ 1)) = -2 := by
    unfold apg_pair
    rw [show (∑ i, ggSWordR X ψγ (Pi.single kγ 1) i *
            ∑ j, X i j * ggSWord X ψ₀ (Pi.single k₀ 1) j)
          = ∑ i, ∑ j, ggSWordR X ψγ (Pi.single kγ 1) i * X i j *
              ggSWord X ψ₀ (Pi.single k₀ 1) j by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    exact hP2
  have hconj : ggSWord X (ψ₀ ++ (ψ₀.reverse ++ ψγ)) (Pi.single kγ 1)
      = ggSWord X ψγ (Pi.single kγ 1) := by
    rw [← List.append_assoc, apg_sWord_append,
      apg_sWord_append_reverse X hX ψ₀ (ggSWord X ψγ (Pi.single kγ 1))]
  have hconjR : ggSWordR X (ψ₀ ++ (ψ₀.reverse ++ ψγ)) (Pi.single kγ 1)
      = ggSWordR X ψγ (Pi.single kγ 1) := by
    rw [← List.append_assoc, apg_sWordR_append,
      apg_sWordR_append_reverse X hX ψ₀ (ggSWordR X ψγ (Pi.single kγ 1))]
  have h1' : ∑ j, ggSWord X (ψ₀.reverse ++ ψγ) (Pi.single kγ 1) j * X k₀ j = -2 := by
    have hg : ggSWord X (ψ₀.reverse ++ ψγ) (Pi.single kγ 1)
        = ggSWord X ψ₀.reverse (ggSWord X ψγ (Pi.single kγ 1)) := by
      rw [apg_sWord_append]
    have hinv := apg_pair_word_inv X hX ψ₀ (Pi.single k₀ 1)
      (ggSWord X ψ₀.reverse (ggSWord X ψγ (Pi.single kγ 1)))
    rw [← apg_sWord_append,
      apg_sWord_append_reverse X hX ψ₀ (ggSWord X ψγ (Pi.single kγ 1))] at hinv
    rw [hP1'] at hinv
    rw [apg_pair_single_left] at hinv
    rw [hg, hinv]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2' : ∑ i, ggSWordR X (ψ₀.reverse ++ ψγ) (Pi.single kγ 1) i * X i k₀ = -2 := by
    have hc : ggSWordR X (ψ₀.reverse ++ ψγ) (Pi.single kγ 1)
        = ggSWordR X ψ₀.reverse (ggSWordR X ψγ (Pi.single kγ 1)) := by
      rw [apg_sWordR_append]
    have hinv := apg_pair_word_inv X hX ψ₀.reverse (ggSWordR X ψγ (Pi.single kγ 1))
      (ggSWord X ψ₀ (Pi.single k₀ 1))
    rw [← apg_sWord_append, apg_sWord_reverse_append X hX ψ₀ (Pi.single k₀ 1)] at hinv
    rw [hP2'] at hinv
    rw [apg_pair_single_right] at hinv
    rw [hc]
    exact hinv
  have hp := ggAffinePair_word X hX k₀ kγ (ψ₀.reverse ++ ψγ) h1' h2' m
  constructor
  · have h := congrArg (ggSWord X ψ₀) hp.1
    dsimp only [ggAffineWord] at h
    rw [← apg_sWord_append, ← apg_sWord_gen_word X hX k₀ kγ ψ₀ ψγ m,
      apg_sWord_sub_smul, apg_sWord_add, ← apg_sWord_append, hconj] at h
    exact h
  · have h := congrArg (ggSWordR X ψ₀) hp.2
    dsimp only [ggAffineWord] at h
    rw [← apg_sWordR_append, ← apg_sWordR_gen_word X hX k₀ kγ ψ₀ ψγ m,
      apg_sWordR_sub_smul, apg_sWordR_add, ← apg_sWordR_append, hconjR] at h
    exact h

end CFSG.StandardType
