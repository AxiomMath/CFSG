module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootGen

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}

@[expose] def wt (d : Fin r → Kˣ) (j : Fin r ⊕ Fin r) : Kˣ := Sum.elim d d⁻¹ j

theorem wt_inl (d : Fin r → Kˣ) (k : Fin r) : wt d (Sum.inl k) = d k := rfl

theorem wt_inr (d : Fin r → Kˣ) (k : Fin r) : wt d (Sum.inr k) = (d k)⁻¹ := rfl

theorem wt_swap (d : Fin r → Kˣ) (j : Fin r ⊕ Fin r) : wt d j.swap = (wt d j)⁻¹ := by
  rcases j with k | k <;> simp [wt]

omit [Module K A] in
theorem hypVec_fst (j c : Fin r ⊕ Fin r) : (hypVec K A j).1 c = if c = j then 1 else 0 := by
  simp [hypVec, Pi.single_apply]

omit [Module K A] in
theorem hypVec_snd (j : Fin r ⊕ Fin r) : (hypVec K A j).2 = 0 := rfl

@[expose] def torH (K : Type) [Field K] (A : Type) [AddCommGroup A] [Module K A] (r : ℕ) :
    (Fin r → Kˣ) →* ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  (prodHom A).comp (torusElt r K)

theorem torH_apply (d : Fin r → Kˣ) (v : (Fin r ⊕ Fin r → K) × A) :
    torH K A r d v = (torusElt r K d v.1, v.2) := rfl

theorem torH_hypVec (d : Fin r → Kˣ) (j : Fin r ⊕ Fin r) :
    torH K A r d (hypVec K A j) = (wt d j : K) • hypVec K A j := by
  refine Prod.ext (funext fun c => ?_) ?_
  · rw [torH_apply]
    simp only [hypVec_fst, torusElt_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    by_cases h : c = j
    · subst h; simp [wt]
    · simp [h]
  · simp [torH_apply, hypVec_snd]

theorem torH_snd (d : Fin r → Kˣ) (v : (Fin r ⊕ Fin r → K) × A) : (torH K A r d v).2 = v.2 := rfl

theorem torH_fst (d : Fin r → Kˣ) (v : (Fin r ⊕ Fin r → K) × A) (c : Fin r ⊕ Fin r) :
    (torH K A r d v).1 c = (wt d c : K) * v.1 c := rfl

theorem torH_mem_orth (qA : QuadraticForm K A) (d : Fin r → Kˣ) :
    torH K A r d ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [quadTail_apply, quadTail_apply, torH_snd, quadPlus_apply, quadPlus_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [torH_fst, torH_fst]
  calc ((wt d (Sum.inl i) : Kˣ) : K) * v.1 (Sum.inl i) * ((wt d (Sum.inr i) : Kˣ) * v.1 (Sum.inr i)) =
      (((wt d (Sum.inl i) : Kˣ) : K) * (wt d (Sum.inr i) : Kˣ)) * (v.1 (Sum.inl i) * v.1 (Sum.inr i)) := by ring
    _ = _ := by simp [wt]

theorem vec_expand (v : (Fin r ⊕ Fin r → K) × A) :
    v = ∑ j : Fin r ⊕ Fin r, v.1 j • hypVec K A j + ((0 : Fin r ⊕ Fin r → K), v.2) := by
  refine Prod.ext (funext fun c => ?_) ?_
  · rw [Prod.fst_add, Prod.fst_sum, Pi.add_apply, Finset.sum_apply]
    simp only [Prod.smul_fst, Pi.smul_apply, hypVec_fst, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply, add_zero]
  · rw [Prod.snd_add, Prod.snd_sum]
    simp [hypVec_snd]

variable (qA : QuadraticForm K A)

@[expose] def rEl (t : K) (j j' : Fin r ⊕ Fin r) :
    ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  eichler (quadTail r qA) (hypVec K A j'.swap) (t • hypVec K A j)

theorem polar_rEl_aux {j j' : Fin r ⊕ Fin r} (h : coordIdx j ≠ coordIdx j') (t : K) :
    polar (quadTail r qA) (hypVec K A j'.swap) (t • hypVec K A j) = 0 := by
  apply polar_hypVec_smul_hypVec
  intro hj
  apply h
  rw [hj, Sum.swap_swap]

theorem rEl_apply {j j' : Fin r ⊕ Fin r} (h : coordIdx j ≠ coordIdx j') (t : K)
    (x : (Fin r ⊕ Fin r → K) × A) :
    rEl qA t j j' x = x + (x.1 j' * t) • hypVec K A j - (t * x.1 j.swap) • hypVec K A j'.swap := by
  have hu : quadTail r qA (hypVec K A j'.swap) = 0 := quadTail_hypVec _
  have hw := polar_rEl_aux qA h t
  unfold rEl
  rw [eichler_apply hu hw, polar_hypVec, Sum.swap_swap, polar_smul_right_eq, polar_hypVec]
  have hQw : quadTail r qA (t • hypVec K A j) = 0 := by
    rw [map_smul_eq_sq, quadTail_hypVec, mul_zero]
  rw [hQw, zero_mul, add_zero, smul_smul]

theorem rEl_apply_hypVec {j j' : Fin r ⊕ Fin r} (h : coordIdx j ≠ coordIdx j') (t : K) (i : Fin r ⊕ Fin r) :
    rEl qA t j j' (hypVec K A i) =
      hypVec K A i + (if i = j' then t else 0) • hypVec K A j -
        (if i = j.swap then t else 0) • hypVec K A j'.swap := by
  rw [rEl_apply qA h]
  have e1 : (hypVec K A i).1 j' = if i = j' then 1 else 0 := by
    rw [hypVec_fst]
    by_cases hi : i = j'
    · simp [hi]
    · have : j' ≠ i := fun h' => hi h'.symm
      simp [hi, this]
  have e2 : (hypVec K A i).1 j.swap = if i = j.swap then 1 else 0 := by
    rw [hypVec_fst]
    by_cases hi : i = j.swap
    · simp [hi]
    · have : j.swap ≠ i := fun h' => hi h'.symm
      simp [hi, this]
  rw [e1, e2]
  split_ifs <;> simp

theorem rEl_mem_orth (t : K) (j j' : Fin r ⊕ Fin r) :
    rEl qA t j j' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) :=
  eichler_mem_orthogonalGroup _ _ _

theorem rEl_swap [CharP K 2] {j j' : Fin r ⊕ Fin r} (h : coordIdx j ≠ coordIdx j') (t : K) :
    rEl qA t j j' = rEl qA t j'.swap j.swap := by
  have h' : coordIdx j'.swap ≠ coordIdx j.swap := by
    rw [coordIdx_swap, coordIdx_swap]; exact fun e => h e.symm
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext x : 1
  rw [rEl_apply qA h, rEl_apply qA h', Sum.swap_swap, Sum.swap_swap]
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_smul, ← neg_smul, CharTwo.neg_eq, CharTwo.neg_eq]
  module

end CFSG.RankThree.PartOne.K159H
