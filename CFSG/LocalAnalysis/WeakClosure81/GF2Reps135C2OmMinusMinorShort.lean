module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusMinorTri

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private noncomputable def o8mMS_block
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun a e => M (.inl a) (.inl e)

private noncomputable def o8mMS_fRow
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) : Fin 3 → K :=
  fun e => M (.inr (.inl 2)) (.inl e)

private noncomputable def o8mMS_gRow (b c : K)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) (w : Fin 2 → K) :
    Fin 3 → K :=
  fun e => ∑ k : Fin 3 ⊕ Fin 3 ⊕ Fin 2,
    QuadraticMap.polar (quadMinus 4 K b c) (Pi.single k 1) (planeVec 4 w) * M k (.inl e)

private noncomputable def o8mMS_D (b c : K)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) (w : Fin 2 → K) : K :=
  (Matrix.updateRow (o8mMS_block M) 2 (o8mMS_gRow b c M w)).det

private noncomputable def o8mMS_Df
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) : K :=
  (Matrix.updateRow (o8mMS_block M) 2 (o8mMS_fRow M)).det

variable (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

omit [Finite K] in
private theorem o8mMS_mat_shortRoot_apply (p : Fin 2 → K) (a : Fin 3)
    (k : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    mat 4 (twShortRoot 4 hirrQ 2 true (.ofAdd p)) (.inl a) k =
      (if (.inl a : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = k then 1 else 0) +
        (QuadraticMap.polar (quadMinus 4 K b c) (Pi.single k 1) (planeVec 4 p) +
          planeNorm b c p * (if (.inr (.inl 2) : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = k then 1 else 0)) *
          (if a = 2 then 1 else 0) := by
  rw [mat_twShortRoot_apply, CharTwo.sub_eq_add]
  simp only [Bool.not_true]
  rw [show (minusPos 4 2 false : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = .inr (.inl 2) from rfl,
    show (minusPos 4 2 true : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = .inl 2 from rfl,
    show (planeVec 4 p (.inl a) : K) = 0 from planeVec_apply_minusPos 4 p a true]
  simp only [mul_zero, add_zero, Sum.inl.injEq]

omit [Finite K] in
private theorem o8mMS_mul_shortRoot_row
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (p : Fin 2 → K) (a e : Fin 3) :
    (mat 4 (twShortRoot 4 hirrQ 2 true (.ofAdd p)) * M) (.inl a) (.inl e) =
      M (.inl a) (.inl e) +
        (if a = 2 then 1 else 0) *
          (o8mMS_gRow b c M p e + planeNorm b c p * o8mMS_fRow M e) := by
  rw [Matrix.mul_apply]
  simp_rw [o8mMS_mat_shortRoot_apply]
  have h1 : ∀ x : Fin 3 ⊕ Fin 3 ⊕ Fin 2,
      ((if (.inl a : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = x then (1 : K) else 0) +
          (QuadraticMap.polar (quadMinus 4 K b c) (Pi.single x 1) (planeVec 4 p) +
              planeNorm b c p * (if (.inr (.inl 2) : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = x then
                (1 : K) else 0)) * (if a = 2 then (1 : K) else 0)) * M x (.inl e) =
        (if (.inl a : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = x then (1 : K) else 0) * M x (.inl e) +
          (if a = 2 then (1 : K) else 0) *
            (QuadraticMap.polar (quadMinus 4 K b c) (Pi.single x 1) (planeVec 4 p) *
              M x (.inl e)) +
          ((if a = 2 then (1 : K) else 0) * planeNorm b c p) *
            ((if (.inr (.inl 2) : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = x then (1 : K) else 0) *
              M x (.inl e)) := by
    intro x
    ring
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hA : (∑ x : Fin 3 ⊕ Fin 3 ⊕ Fin 2,
      (if (.inl a : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = x then (1 : K) else 0) * M x (.inl e)) =
      M (.inl a) (.inl e) := by simp
  have hD : (∑ x : Fin 3 ⊕ Fin 3 ⊕ Fin 2,
      (if (.inr (.inl 2) : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = x then (1 : K) else 0) * M x (.inl e)) =
      M (.inr (.inl 2)) (.inl e) := by simp
  rw [hA, hD]
  simp only [o8mMS_gRow, o8mMS_fRow]
  ring

omit [Finite K] [CharP K 2] in
private theorem o8mMS_minor_eq_det
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    o8mMinor 2 M = (o8mMS_block M).det := by
  rw [o8mMinor]
  congr 1

omit [Finite K] in
private theorem o8mMS_minor_shortRoot
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) (p : Fin 2 → K) :
    o8mMinor 2 (mat 4 (twShortRoot 4 hirrQ 2 true (.ofAdd p)) * M) =
      o8mMinor 2 M +
        (Matrix.updateRow (o8mMS_block M) 2 (o8mMS_gRow b c M p)).det +
        planeNorm b c p * (Matrix.updateRow (o8mMS_block M) 2 (o8mMS_fRow M)).det := by
  rw [o8mMS_minor_eq_det (mat 4 (twShortRoot 4 hirrQ 2 true (.ofAdd p)) * M), o8mMS_minor_eq_det M]
  have hblk : o8mMS_block (mat 4 (twShortRoot 4 hirrQ 2 true (.ofAdd p)) * M) =
      Matrix.updateRow (o8mMS_block M) 2 ((o8mMS_block M) 2 +
        (o8mMS_gRow b c M p + planeNorm b c p • o8mMS_fRow M)) := by
    ext a e
    show (mat 4 (twShortRoot 4 hirrQ 2 true (.ofAdd p)) * M) (.inl a) (.inl e) = _
    rw [o8mMS_mul_shortRoot_row]
    simp only [o8mMS_block, o8mMS_fRow, Matrix.updateRow_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    by_cases ha : a = 2 <;> simp [ha]
  rw [hblk, Matrix.det_updateRow_add, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self]
  ring

private theorem o8mMS_mat_nTwo_apply (a : Fin 3) (k : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    mat 4 ((o8mDatum hirrQ).n 2) (.inl a) k =
      (if a = 2 then
        -(if (.inr (.inl 2) : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = k then (1 : K) else 0)
        else (if (.inl a : Fin 3 ⊕ Fin 3 ⊕ Fin 2) = k then (1 : K) else 0)) := by
  rw [o8mDatum_n, minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num), mat_apply]
  rcases k with j | j | t
  · rw [show (Pi.single (.inl j) (1 : K) : Vm 4 K) = minusVec 4 j true from rfl,
      spinAction_shortWeyl_minusVec]
    fin_cases a <;> fin_cases j <;>
      simp [minusVec_eq_single, minusPos, longWeylSign, shortWeylBool, CharTwo.neg_eq]
  · rw [show (Pi.single (.inr (.inl j)) (1 : K) : Vm 4 K) = minusVec 4 j false from rfl,
      spinAction_shortWeyl_minusVec]
    fin_cases a <;> fin_cases j <;>
      simp [minusVec_eq_single, minusPos, longWeylSign, shortWeylBool, CharTwo.neg_eq]
  · have hplane : (Pi.single (.inr (.inr t)) (1 : K) : Vm 4 K) =
        planeVec 4 (Pi.single t 1) := by
      funext x
      rcases x with i | i | t' <;> simp [planeVec, Pi.single_apply]
    rw [hplane, spinAction_shortWeyl_planeVec]
    rw [show (planeVec 4 (planeRefl b c planeOne (Pi.single t 1)) (.inl a) : K) = 0 from
      planeVec_apply_minusPos 4 _ a true]
    fin_cases a <;> fin_cases t <;>
      simp [CharTwo.neg_eq]

omit [Finite K] [CharP K 2] in
private theorem o8mMS_sum_delta (c : Fin 3 ⊕ Fin 3 ⊕ Fin 2)
    (f : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :
    (∑ k, (if c = k then (1 : K) else 0) * f k) = f c := by
  simp

private theorem o8mMS_minor_nTwo
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    o8mMinor 2 (mat 4 ((o8mDatum hirrQ).n 2) * M) = o8mMS_Df M := by
  rw [o8mMS_minor_eq_det (mat 4 ((o8mDatum hirrQ).n 2) * M), o8mMS_Df]
  have hblk : o8mMS_block (mat 4 ((o8mDatum hirrQ).n 2) * M) =
      Matrix.updateRow (o8mMS_block M) 2 (-(o8mMS_fRow M)) := by
    ext a e
    change (mat 4 ((o8mDatum hirrQ).n 2) * M) (.inl a) (.inl e) = _
    by_cases ha : a = 2
    · rw [Matrix.mul_apply]
      simp_rw [o8mMS_mat_nTwo_apply, if_pos ha]
      simp only [o8mMS_block, Matrix.updateRow_apply, Matrix.of_apply, neg_mul, if_pos ha]
      rw [Finset.sum_neg_distrib, o8mMS_sum_delta]
      rfl
    · rw [Matrix.mul_apply]
      simp_rw [o8mMS_mat_nTwo_apply, if_neg ha]
      simp only [o8mMS_block, Matrix.updateRow_apply, Matrix.of_apply, if_neg ha]
      rw [o8mMS_sum_delta]
  rw [hblk]
  have hneg : -(o8mMS_fRow M) = o8mMS_fRow M := by
    funext e
    rw [Pi.neg_apply, CharTwo.neg_eq]
  rw [hneg]

omit [Finite K] [CharP K 2] in
private theorem o8mMS_gRow_add
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (w w' : Fin 2 → K) :
    o8mMS_gRow b c M (w + w') = o8mMS_gRow b c M w + o8mMS_gRow b c M w' := by
  funext e
  simp only [o8mMS_gRow, Pi.add_apply, planeVec_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [QuadraticMap.polar_add_right]
  ring

omit [Finite K] [CharP K 2] in
private theorem o8mMS_D_add
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (w w' : Fin 2 → K) :
    o8mMS_D b c M (w + w') = o8mMS_D b c M w + o8mMS_D b c M w' := by
  rw [o8mMS_D, o8mMS_gRow_add, o8mMS_D, o8mMS_D, Matrix.det_updateRow_add]

private theorem o8mMS_b_ne_zero (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  have h := discr_ne_zero_of_finite (K := K) hirrQ
  have h4 : (4 : K) = 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num, CharTwo.two_eq_zero, zero_mul]
  rw [h4, zero_mul, sub_zero] at h
  exact fun hb => h (by rw [hb]; simp)

private theorem o8mMS_shortRoot_mem (p : Fin 2 → K) :
    twShortRoot 4 hirrQ 2 true (.ofAdd p) ∈ (o8mDatum hirrQ).X 2 := by
  rw [o8mDatum_X, minusRootGroup_single_of_not_lt 4 hirrQ (k := 2) (by norm_num)]
  exact ⟨Multiplicative.ofAdd p, rfl⟩

private noncomputable def o8mMS_p2 : Fin 2 → K := ![0, 1]

private noncomputable def o8mMS_p3 : Fin 2 → K := ![1, 1]

omit [Finite K] [CharP K 2] in
private theorem o8mMS_planeOne_add_p2 : (planeOne : Fin 2 → K) + o8mMS_p2 = o8mMS_p3 := by
  funext t
  fin_cases t <;> simp [planeOne, o8mMS_p2, o8mMS_p3]

omit [Finite K] in
private theorem o8mMS_norm_sum :
    planeNorm b c (planeOne : Fin 2 → K) + planeNorm b c o8mMS_p2 + planeNorm b c o8mMS_p3 =
      b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [o8mMS_p2, o8mMS_p3, planeOne, planeNorm, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, Matrix.cons_val_fin_one]
  linear_combination (1 + c) * h2

private theorem o8mMS_D_add_norm_mul_Df_eq_zero
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (hM : ∀ x ∈ (o8mDatum hirrQ).X 2, o8mMinor 2 (mat 4 x * M) = o8mMinor 2 M)
    (p : Fin 2 → K) :
    o8mMS_D b c M p + planeNorm b c p * o8mMS_Df M = 0 := by
  have h1 := o8mMS_minor_shortRoot hirrQ M p
  rw [hM _ (o8mMS_shortRoot_mem hirrQ p)] at h1
  rw [o8mMS_D, o8mMS_Df]
  rw [add_assoc] at h1
  exact add_left_cancel (h1.symm.trans (add_zero _).symm)

private theorem o8mMS_D_eq_norm_mul_Df
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (hM : ∀ x ∈ (o8mDatum hirrQ).X 2, o8mMinor 2 (mat 4 x * M) = o8mMinor 2 M)
    (p : Fin 2 → K) :
    o8mMS_D b c M p = planeNorm b c p * o8mMS_Df M := by
  have h := eq_neg_of_add_eq_zero_left (o8mMS_D_add_norm_mul_Df_eq_zero hirrQ M hM p)
  rwa [CharTwo.neg_eq] at h

private theorem o8mMS_b_mul_Df_eq_zero
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (hM : ∀ x ∈ (o8mDatum hirrQ).X 2, o8mMinor 2 (mat 4 x * M) = o8mMinor 2 M) :
    b * o8mMS_Df M = 0 := by
  have e1 := o8mMS_D_eq_norm_mul_Df hirrQ M hM (planeOne : Fin 2 → K)
  have e2 := o8mMS_D_eq_norm_mul_Df hirrQ M hM o8mMS_p2
  have e3 := o8mMS_D_eq_norm_mul_Df hirrQ M hM o8mMS_p3
  have hDadd : o8mMS_D b c M o8mMS_p3 = o8mMS_D b c M planeOne + o8mMS_D b c M o8mMS_p2 := by
    have h : o8mMS_D b c M ((planeOne : Fin 2 → K) + o8mMS_p2) =
        o8mMS_D b c M planeOne + o8mMS_D b c M o8mMS_p2 :=
      o8mMS_D_add M (planeOne : Fin 2 → K) o8mMS_p2
    rwa [o8mMS_planeOne_add_p2] at h
  have e12 : (planeNorm b c planeOne + planeNorm b c o8mMS_p2) * o8mMS_Df M =
      planeNorm b c o8mMS_p3 * o8mMS_Df M := by
    calc (planeNorm b c planeOne + planeNorm b c o8mMS_p2) * o8mMS_Df M
        = planeNorm b c planeOne * o8mMS_Df M + planeNorm b c o8mMS_p2 * o8mMS_Df M := by
          ring
      _ = o8mMS_D b c M planeOne + o8mMS_D b c M o8mMS_p2 := by rw [← e1, ← e2]
      _ = o8mMS_D b c M o8mMS_p3 := hDadd.symm
      _ = planeNorm b c o8mMS_p3 * o8mMS_Df M := e3
  have key : (planeNorm b c planeOne + planeNorm b c o8mMS_p2) * o8mMS_Df M +
      planeNorm b c o8mMS_p3 * o8mMS_Df M = 0 := by
    rw [e12, ← two_mul, CharTwo.two_eq_zero, zero_mul]
  rw [← add_mul, o8mMS_norm_sum] at key
  exact key

theorem o8mMinor_mat_n_two_mul_eq_zero
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (hM : ∀ x ∈ (o8mDatum hirrQ).X 2, o8mMinor 2 (mat 4 x * M) = o8mMinor 2 M) :
    o8mMinor 2 (mat 4 ((o8mDatum hirrQ).n 2) * M) = 0 := by
  rw [o8mMS_minor_nTwo]
  exact (mul_eq_zero.mp (o8mMS_b_mul_Df_eq_zero hirrQ M hM)).resolve_left
    (o8mMS_b_ne_zero hirrQ)

end CFSG.LocalAnalysis.WeakClosure81
