module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusData
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearDelta

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

@[expose] noncomputable def o8mMinor {R : Type*} [CommRing R] (i : Fin 3)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) R) : R :=
  (M.submatrix (fun j : Fin (i + 1) => .inl (Fin.castLE i.isLt j))
    (fun j : Fin (i + 1) => .inl (Fin.castLE i.isLt j))).det

@[expose] noncomputable def o8mMinorProd {R : Type*} [CommRing R] (J : Finset (Fin 3))
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) R) : R :=
  ∏ i ∈ J, o8mMinor i M

private abbrev o8mMT_e (i : Fin 3) : Fin (i + 1) → Fin 3 ⊕ Fin 3 ⊕ Fin 2 :=
  fun j => .inl (Fin.castLE i.isLt j)

private theorem o8mMT_e_injective (i : Fin 3) : Function.Injective (o8mMT_e i) :=
  Sum.inl_injective.comp (Fin.castLE_injective i.isLt)

theorem o8mMinor_one {R : Type*} [CommRing R] (i : Fin 3) :
    o8mMinor i (1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) R) = 1 := by
  change ((1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) R).submatrix
    (o8mMT_e i) (o8mMT_e i)).det = 1
  have hmat : (1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) R).submatrix
      (o8mMT_e i) (o8mMT_e i) = 1 := by
    ext a b
    rw [Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · have hne : o8mMT_e i a ≠ o8mMT_e i b := fun h => hab (o8mMT_e_injective i h)
      rw [if_neg hne, if_neg hab]
  rw [hmat, Matrix.det_one]

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

private theorem o8mMT_epsHt_single (r : Fin 3) (c : ℤ) :
    epsHt 4 (Pi.single r c) = (3 - (r : ℤ)) * c := by
  change (∑ a : Fin 3, ((3 : ℤ) - (a : ℤ)) * (Pi.single r c : Fin 3 → ℤ) a) =
    (3 - (r : ℤ)) * c
  rw [Finset.sum_eq_single r]
  · rw [Pi.single_eq_same]
  · intro d _ hd
    rw [Pi.single_eq_of_ne hd, mul_zero]
  · intro hr
    exact absurd (Finset.mem_univ r) hr

private theorem o8mMT_lev_inl (r : Fin 3) :
    epsHt 4 (minusWt 4 (.inl r : Fin 3 ⊕ Fin 3 ⊕ Fin 2)) = 3 - (r : ℤ) := by
  change epsHt 4 (Pi.single r (1 : ℤ)) = 3 - (r : ℤ)
  rw [o8mMT_epsHt_single]; ring

private theorem o8mMT_lev_inr_inl (r : Fin 3) :
    epsHt 4 (minusWt 4 (.inr (.inl r) : Fin 3 ⊕ Fin 3 ⊕ Fin 2)) = -(3 - (r : ℤ)) := by
  change epsHt 4 (Pi.single r (-1 : ℤ)) = -(3 - (r : ℤ))
  rw [o8mMT_epsHt_single]; ring

private theorem o8mMT_lev_inr_inr (t : Fin 2) :
    epsHt 4 (minusWt 4 (.inr (.inr t) : Fin 3 ⊕ Fin 3 ⊕ Fin 2)) = 0 := by
  change epsHt 4 (0 : Fin 3 → ℤ) = 0
  rw [map_zero]

private theorem o8mMT_lev_e (i : Fin 3) (r : Fin (i + 1)) :
    epsHt 4 (minusWt 4 (o8mMT_e i r)) = 3 - (r : ℤ) := by
  change epsHt 4 (minusWt 4 (.inl (Fin.castLE i.isLt r))) = 3 - (r : ℤ)
  rw [o8mMT_lev_inl]
  exact congrArg (fun n : ℕ => (3 : ℤ) - n) (Fin.val_castLE i.isLt r)

private theorem o8mMT_fin3_le_two (s : Fin 3) : (s : ℤ) ≤ 2 := by
  have := s.isLt
  omega

private theorem o8mMT_lev_e_ge_one (i : Fin 3) (r : Fin (i + 1)) :
    (1 : ℤ) ≤ epsHt 4 (minusWt 4 (o8mMT_e i r)) := by
  rw [o8mMT_lev_e]
  have := r.isLt
  have := i.isLt
  omega

private theorem o8mMT_lev_le_of_notMem_range (i : Fin 3) {r : Fin (i + 1)}
    {d : Fin 3 ⊕ Fin 3 ⊕ Fin 2} (hd : d ∉ Set.range (o8mMT_e i)) :
    epsHt 4 (minusWt 4 d) ≤ epsHt 4 (minusWt 4 (o8mMT_e i r)) := by
  have hr := o8mMT_lev_e_ge_one i r
  rcases d with s | s
  · rw [o8mMT_lev_inl, o8mMT_lev_e]
    have hs : r.val ≤ s.val := by
      by_contra hlt
      push Not at hlt
      have hrs : s.val < i.val + 1 := by have := r.isLt; omega
      exact hd ⟨⟨s.val, hrs⟩, by
        simp only [o8mMT_e]
        rw [show Fin.castLE i.isLt ⟨s.val, hrs⟩ = s from Fin.ext (by simp)]⟩
    omega
  · rcases s with s | t
    · rw [o8mMT_lev_inr_inl]
      have hs := o8mMT_fin3_le_two s
      omega
    · rw [o8mMT_lev_inr_inr]
      omega

private theorem o8mMT_lev_e_lt (i : Fin 3) {p q : Fin (i + 1)} (hpq : p < q) :
    epsHt 4 (minusWt 4 (o8mMT_e i q)) < epsHt 4 (minusWt 4 (o8mMT_e i p)) := by
  rw [o8mMT_lev_e, o8mMT_lev_e]
  omega

private theorem o8mMT_neg_smul_epsHt (a : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    ((-1 : ℤ) • epsHt 4) (minusWt 4 a) = -epsHt 4 (minusWt 4 a) := by
  rw [AddMonoidHom.smul_apply, smul_eq_mul]
  ring

omit [Finite K] [CharP K 2] in
private theorem o8mMT_mul_submatrix_of_row_support {m : Type*} [Fintype m]
    (A M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (ε : m → Fin 3 ⊕ Fin 3 ⊕ Fin 2) (hinj : Function.Injective ε)
    (hA : ∀ r d, d ∉ Set.range ε → A (ε r) d = 0) :
    (A * M).submatrix ε ε = A.submatrix ε ε * M.submatrix ε ε := by
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hsum : (∑ x : Fin 3 ⊕ Fin 3 ⊕ Fin 2, A (ε r) x * M x (ε c)) =
      ∑ x ∈ (Finset.univ : Finset m).image ε, A (ε r) x * M x (ε c) :=
    (Fintype.sum_subset (s := (Finset.univ : Finset m).image ε) (fun x hx => by
      by_contra hmem
      have hr : x ∉ Set.range ε := by
        rintro ⟨a, ha⟩
        exact hmem (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
      exact hx (by rw [hA r x hr, zero_mul]))).symm
  rw [hsum, Finset.sum_image (fun a _ b _ hab => hinj hab)]

omit [Finite K] [CharP K 2] in
private theorem o8mMT_submatrix_mul_of_col_support {m : Type*} [Fintype m]
    (A M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (ε : m → Fin 3 ⊕ Fin 3 ⊕ Fin 2) (hinj : Function.Injective ε)
    (hA : ∀ d j, d ∉ Set.range ε → A d (ε j) = 0) :
    (M * A).submatrix ε ε = M.submatrix ε ε * A.submatrix ε ε := by
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hsum : (∑ x : Fin 3 ⊕ Fin 3 ⊕ Fin 2, M (ε r) x * A x (ε c)) =
      ∑ x ∈ (Finset.univ : Finset m).image ε, M (ε r) x * A x (ε c) :=
    (Fintype.sum_subset (s := (Finset.univ : Finset m).image ε) (fun x hx => by
      by_contra hmem
      have hr : x ∉ Set.range ε := by
        rintro ⟨a, ha⟩
        exact hmem (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
      exact hx (by rw [hA x c hr, mul_zero]))).symm
  rw [hsum, Finset.sum_image (fun a _ b _ hab => hinj hab)]

private theorem o8mMT_idBelow_neg {l : spinGroup (quadMinus 4 K b c)}
    (hl : l ∈ (o8mDatum hirrQ).L) :
    CFSG.LieType.Steinberg.Graded.IdBelow
      (fun a => ((-1 : ℤ) • epsHt 4) (minusWt 4 a)) 1 (mat 4 l) := by
  change l ∈ CFSG.LieType.Steinberg.negUnipotent (minusDatum 4 hirrQ) at hl
  exact idBelow_of_mem_iSup 4 hirrQ (-1) _ (fun γ hγ => ⟨hγ.1, by
    have : CFSG.LieType.Steinberg.ht (ι := Fin 3) γ < 0 := hγ.2
    omega⟩) hl

private theorem o8mMT_idBelow_pos {u : spinGroup (quadMinus 4 K b c)}
    (hu : u ∈ (o8mDatum hirrQ).U) :
    CFSG.LieType.Steinberg.Graded.IdBelow
      (fun a => ((1 : ℤ) • epsHt 4) (minusWt 4 a)) 1 (mat 4 u) := by
  change u ∈ CFSG.LieType.Steinberg.posUnipotent (minusDatum 4 hirrQ) at hu
  exact idBelow_of_mem_iSup 4 hirrQ 1 _ (fun γ hγ => ⟨hγ.1, by
    have : 0 < CFSG.LieType.Steinberg.ht (ι := Fin 3) γ := hγ.2
    omega⟩) hu

private theorem o8mMT_row_support_L {l : spinGroup (quadMinus 4 K b c)}
    (hl : l ∈ (o8mDatum hirrQ).L) (i : Fin 3) (r : Fin (i + 1))
    (d : Fin 3 ⊕ Fin 3 ⊕ Fin 2) (hd : d ∉ Set.range (o8mMT_e i)) :
    mat 4 l (o8mMT_e i r) d = 0 := by
  refine (o8mMT_idBelow_neg hirrQ hl).apply_eq_zero (fun h => hd ⟨r, h⟩) ?_
  rw [o8mMT_neg_smul_epsHt, o8mMT_neg_smul_epsHt]
  linarith [o8mMT_lev_le_of_notMem_range (r := r) i hd]

private theorem o8mMT_col_support_U {u : spinGroup (quadMinus 4 K b c)}
    (hu : u ∈ (o8mDatum hirrQ).U) (i : Fin 3) (d : Fin 3 ⊕ Fin 3 ⊕ Fin 2)
    (j : Fin (i + 1)) (hd : d ∉ Set.range (o8mMT_e i)) :
    mat 4 u d (o8mMT_e i j) = 0 := by
  refine (o8mMT_idBelow_pos hirrQ hu).apply_eq_zero (fun h => hd ⟨j, h.symm⟩) ?_
  simp only [one_smul]
  linarith [o8mMT_lev_le_of_notMem_range (r := j) i hd]

private theorem o8mMT_det_submatrix_L {l : spinGroup (quadMinus 4 K b c)}
    (hl : l ∈ (o8mDatum hirrQ).L) (i : Fin 3) :
    ((mat 4 l).submatrix (o8mMT_e i) (o8mMT_e i)).det = 1 := by
  have hid := o8mMT_idBelow_neg hirrQ hl
  have hlow : ((mat 4 l).submatrix (o8mMT_e i) (o8mMT_e i)).IsLowerTriangular := by
    intro p q hpq
    have hpq' : p < q := hpq
    rw [Matrix.submatrix_apply]
    refine hid.apply_eq_zero (fun h => absurd (o8mMT_e_injective i h) (ne_of_lt hpq)) ?_
    rw [o8mMT_neg_smul_epsHt, o8mMT_neg_smul_epsHt]
    linarith [o8mMT_lev_e_lt i hpq']
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  exact Fintype.prod_eq_one _ (fun r => by
    rw [Matrix.submatrix_apply]
    exact CFSG.LieType.Steinberg.Graded.IdBelow.apply_self (by norm_num) hid (o8mMT_e i r))

private theorem o8mMT_det_submatrix_U {u : spinGroup (quadMinus 4 K b c)}
    (hu : u ∈ (o8mDatum hirrQ).U) (i : Fin 3) :
    ((mat 4 u).submatrix (o8mMT_e i) (o8mMT_e i)).det = 1 := by
  have hid := o8mMT_idBelow_pos hirrQ hu
  have hup : ((mat 4 u).submatrix (o8mMT_e i) (o8mMT_e i)).IsUpperTriangular := by
    intro p q hpq
    have hpq' : q < p := hpq
    rw [Matrix.submatrix_apply]
    refine hid.apply_eq_zero (fun h => absurd (o8mMT_e_injective i h) (ne_of_gt hpq)) ?_
    simp only [one_smul]
    linarith [o8mMT_lev_e_lt i hpq']
  rw [Matrix.det_of_isUpperTriangular hup]
  exact Fintype.prod_eq_one _ (fun r => by
    rw [Matrix.submatrix_apply]
    exact CFSG.LieType.Steinberg.Graded.IdBelow.apply_self (by norm_num) hid (o8mMT_e i r))

private theorem o8mMT_blockDiag_H {h : spinGroup (quadMinus 4 K b c)}
    (hh : h ∈ (o8mDatum hirrQ).H) : BlockDiag 4 (mat 4 h) := by
  change h ∈ (⨆ k, minusTorus 4 hirrQ k) at hh
  refine Subgroup.iSup_induction _ hh (C := fun g => BlockDiag 4 (mat 4 g))
    (fun k y hy => blockDiag_mat_of_mem_minusTorus 4 hirrQ k hy) ?_ fun x y hx hy => ?_
  · rw [mat_one]
    exact blockDiag_one 4
  · rw [mat_mul]
    exact blockDiag_mul 4 hx hy

private theorem o8mMT_col_H_ne_zero {h : spinGroup (quadMinus 4 K b c)}
    (hh : h ∈ (o8mDatum hirrQ).H) (i : Fin 3) (j : Fin (i + 1)) :
    mat 4 h (o8mMT_e i j) (o8mMT_e i j) ≠ 0 := by
  have hD := o8mMT_blockDiag_H hirrQ hh
  intro h0
  have hcol : (fun a => mat 4 h a (o8mMT_e i j)) = 0 := by
    funext a
    by_cases ha : a = o8mMT_e i j
    · subst ha; rw [h0]; rfl
    · rw [hD.apply_eq_zero 4 ha (Or.inr fun t => by simp [o8mMT_e])]; rfl
  have hzero : spinAction (quadMinus 4 K b c) h
      (Pi.single (o8mMT_e i j) (1 : K) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) = 0 := by
    funext a
    rw [Pi.zero_apply, ← mat_apply]
    exact congrFun hcol a
  have hsne : (Pi.single (o8mMT_e i j) (1 : K) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) ≠ 0 := by
    intro hh0
    have h1 := congrFun hh0 (o8mMT_e i j)
    simp at h1
  exact hsne ((spinAction (quadMinus 4 K b c) h).injective (by rw [hzero, map_zero]))

private theorem o8mMT_col_H (hK : Nat.card K = 2) {h : spinGroup (quadMinus 4 K b c)}
    (hh : h ∈ (o8mDatum hirrQ).H) (i : Fin 3) (j : Fin (i + 1)) :
    ∀ a, mat 4 h a (o8mMT_e i j) = (1 : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2)
      (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) a (o8mMT_e i j) := by
  have hD := o8mMT_blockDiag_H hirrQ hh
  have hdiag : mat 4 h (o8mMT_e i j) (o8mMT_e i j) = 1 := by
    rcases CFSG.SeitzReduction.LinearDelta.eq_zero_or_eq_one_of_card_two hK
      (mat 4 h (o8mMT_e i j) (o8mMT_e i j)) with h0 | h1
    · exact absurd h0 (o8mMT_col_H_ne_zero hirrQ hh i j)
    · exact h1
  intro a
  by_cases ha : a = o8mMT_e i j
  · subst ha; rw [Matrix.one_apply_eq, hdiag]
  · rw [Matrix.one_apply_ne ha]
    exact hD.apply_eq_zero 4 ha (Or.inr fun t => by simp [o8mMT_e])

private theorem o8mMT_mul_mat_H_submatrix (hK : Nat.card K = 2)
    {h : spinGroup (quadMinus 4 K b c)} (hh : h ∈ (o8mDatum hirrQ).H) (i : Fin 3)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    (M * mat 4 h).submatrix (o8mMT_e i) (o8mMT_e i) =
      M.submatrix (o8mMT_e i) (o8mMT_e i) := by
  ext a j
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [Finset.sum_eq_single (o8mMT_e i j)]
  · rw [o8mMT_col_H hirrQ hK hh i j (o8mMT_e i j), Matrix.one_apply_eq, mul_one]
  · intro d _ hd
    rw [o8mMT_col_H hirrQ hK hh i j d, Matrix.one_apply_ne hd, mul_zero]
  · simp

theorem o8mMinor_mat_mul_of_mem_L {l : spinGroup (quadMinus 4 K b c)}
    (hl : l ∈ (o8mDatum hirrQ).L) (i : Fin 3)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    o8mMinor i (mat 4 l * M) = o8mMinor i M := by
  change ((mat 4 l * M).submatrix (o8mMT_e i) (o8mMT_e i)).det =
    (M.submatrix (o8mMT_e i) (o8mMT_e i)).det
  rw [o8mMT_mul_submatrix_of_row_support (mat 4 l) M (o8mMT_e i) (o8mMT_e_injective i)
    (fun r d hd => o8mMT_row_support_L hirrQ hl i r d hd)]
  rw [Matrix.det_mul, o8mMT_det_submatrix_L hirrQ hl i, one_mul]

theorem o8mMinor_mul_mat_of_mem_U {u : spinGroup (quadMinus 4 K b c)}
    (hu : u ∈ (o8mDatum hirrQ).U) (i : Fin 3)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    o8mMinor i (M * mat 4 u) = o8mMinor i M := by
  change ((M * mat 4 u).submatrix (o8mMT_e i) (o8mMT_e i)).det =
    (M.submatrix (o8mMT_e i) (o8mMT_e i)).det
  rw [o8mMT_submatrix_mul_of_col_support (mat 4 u) M (o8mMT_e i) (o8mMT_e_injective i)
    (fun d j hd => o8mMT_col_support_U hirrQ hu i d j hd)]
  rw [Matrix.det_mul, o8mMT_det_submatrix_U hirrQ hu i, mul_one]

theorem o8mMinor_mul_mat_of_mem_H (hK : Nat.card K = 2) {h : spinGroup (quadMinus 4 K b c)}
    (hh : h ∈ (o8mDatum hirrQ).H) (i : Fin 3)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    o8mMinor i (M * mat 4 h) = o8mMinor i M := by
  change ((M * mat 4 h).submatrix (o8mMT_e i) (o8mMT_e i)).det =
    (M.submatrix (o8mMT_e i) (o8mMT_e i)).det
  rw [o8mMT_mul_mat_H_submatrix hirrQ hK hh i M]

end CFSG.LocalAnalysis.WeakClosure81
