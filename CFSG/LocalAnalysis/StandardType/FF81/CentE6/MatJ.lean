module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatSStruct
import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open scoped Pointwise

private theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  exact this c

private theorem elem_coe (i j : Fin 6) (h : i ≠ j) :
    ((elem i j : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 + Matrix.single i j 1 := by
  simp [elem, dif_neg h, Matrix.SpecialLinearGroup.transvection_coe]

private theorem elem_inv_self (i j : Fin 6) (h : i ≠ j) : (elem i j)⁻¹ = elem i j := by
  simp only [elem, dif_neg h]
  rw [Matrix.SpecialLinearGroup.transvection_inv]
  congr 1

private def embIdx (a : Fin 4) : Fin 6 := ⟨a.val + 1, by omega⟩

private def emb (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun i j =>
    if h : 1 ≤ i.val ∧ i.val ≤ 4 ∧ 1 ≤ j.val ∧ j.val ≤ 4 then
      A ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    else if i = j then 1 else 0

private theorem emb_one : emb (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb]

private theorem emb_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    emb (A * B) = emb A * emb B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb, Matrix.mul_apply, Fin.sum_univ_succ]

private def midBlock {R : Type*} (G : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  G.submatrix embIdx embIdx

private theorem succ_succAbove_last :
    (Fin.succ ∘ (Fin.succAbove (4 : Fin 5))) = embIdx := by
  have h : (Fin.succAbove (4 : Fin 5)) = Fin.castSucc := by
    rw [show (4 : Fin 5) = Fin.last 4 from rfl, Fin.succAbove_last]
  rw [h]
  funext a
  rfl

private theorem midBlock_emb (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    midBlock (emb A) = A := by
  ext a b
  simp [midBlock, emb, embIdx]

private theorem det_of_firstcol_lastrow {R : Type*} [CommRing R]
    (G : Matrix (Fin 6) (Fin 6) R) (l : R)
    (h0 : ∀ i, G i 0 = if i = 0 then l else 0)
    (h5 : ∀ j, G 5 j = if j = 5 then l else 0) :
    G.det = l * l * (midBlock G).det := by
  rw [Matrix.det_succ_column_zero]
  rw [Finset.sum_eq_single (0 : Fin 6)]
  · rw [Fin.succAbove_zero]
    rw [h0 0, if_pos rfl]
    rw [Matrix.det_succ_row (G.submatrix Fin.succ Fin.succ) 4]
    rw [Finset.sum_eq_single (4 : Fin 5)]
    · simp only [Fin.val_zero, pow_zero, one_mul]
      rw [Matrix.submatrix_apply]
      rw [show (Fin.succ (4 : Fin 5) : Fin 6) = 5 from rfl, h5 5, if_pos rfl]
      rw [show (-1 : R) ^ ((4 : Fin 5).val + (4 : Fin 5).val) = 1 by norm_num]
      rw [Matrix.submatrix_submatrix, succ_succAbove_last]
      simp only [midBlock]
      ring
    · intro j _ hj
      rw [Matrix.submatrix_apply]
      have hj5 : (Fin.succ j : Fin 6) ≠ 5 := by
        intro h
        exact hj (Fin.ext (by simpa using congrArg Fin.val h))
      rw [show (Fin.succ (4 : Fin 5) : Fin 6) = 5 from rfl, h5 (Fin.succ j), if_neg hj5]
      simp
    · intro h
      exact absurd (Finset.mem_univ 4) h
  · intro i _ hi
    rw [h0 i, if_neg hi]
    simp
  · intro h
    exact absurd (Finset.mem_univ 0) h

private theorem det_emb (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : (emb A).det = A.det := by
  rw [det_of_firstcol_lastrow (emb A) 1]
  · rw [midBlock_emb]
    ring
  · intro i
    fin_cases i <;> simp [emb]
  · intro j
    fin_cases j <;> simp [emb]

private noncomputable def embSL : SL(4, ZMod 2) →* SL(6, ZMod 2) where
  toFun A := ⟨emb A, by rw [det_emb]; exact A.2⟩
  map_one' := Subtype.ext emb_one
  map_mul' A B := Subtype.ext (emb_mul A B)

private theorem embSL_apply (A : SL(4, ZMod 2)) :
    (embSL A : Matrix (Fin 6) (Fin 6) (ZMod 2)) = emb A := rfl

private theorem embIdx_ne {i j : Fin 4} (h : i ≠ j) : embIdx i ≠ embIdx j := by
  intro hij
  exact h (Fin.ext (by simpa [embIdx] using congrArg Fin.val hij))

private theorem emb_single (i j : Fin 4) :
    emb (1 + Matrix.single i j (1 : ZMod 2)) =
      1 + Matrix.single (embIdx i) (embIdx j) 1 := by
  fin_cases i <;> fin_cases j <;>
    ext a b <;> fin_cases a <;> fin_cases b <;> decide

private theorem embSL_transvection_one (i j : Fin 4) (hij : i ≠ j) :
    embSL (Matrix.SpecialLinearGroup.transvection hij 1) = elem (embIdx i) (embIdx j) := by
  apply Subtype.ext
  rw [embSL_apply, elem_coe _ _ (embIdx_ne hij)]
  rw [show ((Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) : SL(4, ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + Matrix.single i j 1 from
    Matrix.SpecialLinearGroup.transvection_coe hij 1]
  exact emb_single i j

private theorem range_embSL_le_Jgrp : embSL.range ≤ Jgrp := by
  rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 4)
    (K := ZMod 2), MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro _ ⟨A, hA, rfl⟩
  rcases hA with ⟨i, j, hij, c, rfl⟩
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero]
    simp
  · rw [embSL_transvection_one i j hij]
    exact Subgroup.subset_closure ⟨embIdx i, embIdx j, embIdx_ne hij, by simp [embIdx],
      by simp [embIdx], by simp [embIdx], by simp [embIdx], rfl⟩

private theorem embIdx_pred {i : Fin 6} (h1 : 1 ≤ i.val) (h4 : i.val ≤ 4) :
    embIdx ⟨i.val - 1, by omega⟩ = i := by
  ext
  simp [embIdx]
  omega

private theorem Jgrp_le_range_embSL : Jgrp ≤ embSL.range := by
  unfold Jgrp
  rw [Subgroup.closure_le]
  rintro g ⟨i, j, hij, hi1, hi4, hj1, hj4, rfl⟩
  change elem i j ∈ embSL.range
  rw [MonoidHom.mem_range]
  have hii : embIdx ⟨i.val - 1, by omega⟩ = i := embIdx_pred hi1 hi4
  have hjj : embIdx ⟨j.val - 1, by omega⟩ = j := embIdx_pred hj1 hj4
  have hij' : (⟨i.val - 1, by omega⟩ : Fin 4) ≠ ⟨j.val - 1, by omega⟩ := by
    intro h; exact hij (by rw [← hii, ← hjj, h])
  refine ⟨Matrix.SpecialLinearGroup.transvection hij' 1, ?_⟩
  rw [embSL_transvection_one _ _ hij', hii, hjj]

private theorem mem_Jgrp_iff (g : SL(6, ZMod 2)) :
    g ∈ Jgrp ↔ g.1 0 0 = 1 ∧ g.1 5 5 = 1 ∧
      (∀ i : Fin 6, i ≠ 0 → g.1 i 0 = 0) ∧ (∀ j : Fin 6, j ≠ 0 → g.1 0 j = 0) ∧
      (∀ i : Fin 6, i ≠ 5 → g.1 i 5 = 0) ∧ (∀ j : Fin 6, j ≠ 5 → g.1 5 j = 0) := by
  constructor
  · intro hg
    obtain ⟨A, hA⟩ := Jgrp_le_range_embSL hg
    subst hA
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [embSL_apply, emb]
    · simp [embSL_apply, emb]
    · intro i hi; fin_cases i <;> simp_all [embSL_apply, emb]
    · intro j hj; fin_cases j <;> simp_all [embSL_apply, emb]
    · intro i hi; fin_cases i <;> simp_all [embSL_apply, emb]
    · intro j hj; fin_cases j <;> simp_all [embSL_apply, emb]
  · rintro ⟨h00, h55, hi0, h0j, hi5, h5j⟩
    refine range_embSL_le_Jgrp ?_
    rw [MonoidHom.mem_range]
    refine ⟨⟨midBlock g.1, ?hdet⟩, ?heq⟩
    · have h := det_of_firstcol_lastrow g.1 1 ?_ ?_
      · rw [one_mul, one_mul] at h
        rw [← h]
        exact g.2
      · intro i
        by_cases hi : i = 0
        · subst hi; simpa using h00
        · rw [hi0 i hi, if_neg hi]
      · intro j
        by_cases hj : j = 5
        · subst hj; simpa using h55
        · rw [h5j j hj, if_neg hj]
    · apply Subtype.ext
      ext i j
      change emb (midBlock g.1) i j = g.1 i j
      fin_cases i <;> fin_cases j <;>
        simp [emb, midBlock, embIdx, h00, h55, hi0, h0j, hi5, h5j]

private theorem emb_first_col (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    ∀ i, emb A i 0 = if i = 0 then 1 else 0 := by
  intro i; fin_cases i <;> simp [emb]

private theorem midBlock_mul_of_left (G H : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (hG0 : ∀ i, G i 0 = if i = 0 then 1 else 0)
    (hH5 : ∀ j, H 5 j = if j = 5 then 1 else 0) :
    midBlock (G * H) = midBlock G * midBlock H := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [midBlock, Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four, embIdx, hG0, hH5]

private theorem det_of_firstcol {R : Type*} [CommRing R]
    (G : Matrix (Fin 6) (Fin 6) R) (l : R)
    (h0 : ∀ i, G i 0 = if i = 0 then l else 0) :
    G.det = l * (G.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero]
  rw [Finset.sum_eq_single (0 : Fin 6)]
  · rw [Fin.succAbove_zero, h0 0, if_pos rfl]; simp
  · intro i _ hi; rw [h0 i, if_neg hi]; simp
  · intro h; exact absurd (Finset.mem_univ 0) h

private theorem mem_normalizer_closure_of_conj {G : Type*} [Group G] [Finite G] {X : Set G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ Subgroup.closure X) :
    g ∈ Subgroup.normalizer (Subgroup.closure X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    change g * x * g⁻¹ ∈ Subgroup.closure X
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem elem_conj_zero_eq (i j : Fin 6) (hij : i ≠ j) (hi0 : i ≠ 0) (hj0 : j ≠ 0) :
    elem i j * elem 0 i * (elem i j)⁻¹ = elem 0 i * elem 0 j := by
  fin_cases i <;> fin_cases j <;>
    (first
      | exact absurd rfl hij
      | exact absurd rfl hi0
      | exact absurd rfl hj0
      | (rw [elem_inv_self _ _ hij]; decide))

private theorem elem_conj_zero_ne (i j k : Fin 6) (hij : i ≠ j) (hi0 : i ≠ 0) (hj0 : j ≠ 0)
    (hk0 : k ≠ 0) (hki : k ≠ i) :
    elem i j * elem 0 k * (elem i j)⁻¹ = elem 0 k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    (first | exact absurd rfl hij | exact absurd rfl hi0 | exact absurd rfl hj0 |
      exact absurd rfl hk0 | exact absurd rfl hki | (rw [elem_inv_self _ _ hij]; decide))

private theorem elem_conj_five_ne (i j k : Fin 6) (hij : i ≠ j) (hi5 : i ≠ 5) (hj5 : j ≠ 5)
    (hk5 : k ≠ 5) (hkj : k ≠ j) :
    elem i j * elem k 5 * (elem i j)⁻¹ = elem k 5 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    (first | exact absurd rfl hij | exact absurd rfl hi5 | exact absurd rfl hj5 |
      exact absurd rfl hk5 | exact absurd rfl hkj | (rw [elem_inv_self _ _ hij]; decide))

private theorem elem_conj_five_eq (i j : Fin 6) (hij : i ≠ j) (hi5 : i ≠ 5) (hj5 : j ≠ 5) :
    elem i j * elem j 5 * (elem i j)⁻¹ = elem j 5 * elem i 5 := by
  fin_cases i <;> fin_cases j <;>
    (first | exact absurd rfl hij | exact absurd rfl hi5 | exact absurd rfl hj5 |
      (rw [elem_inv_self _ _ hij]; decide))

private theorem embIdx_injective : Function.Injective embIdx := by
  intro a b h
  by_contra hab
  exact embIdx_ne hab h

private theorem midBlock_one : midBlock (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
  ext a b
  simp [midBlock, Matrix.one_apply, embIdx_injective.eq_iff]

private theorem mul_shape_of_shapes (G H : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (hG0 : ∀ i, G i 0 = if i = 0 then 1 else 0)
    (hG5 : ∀ j, G 5 j = if j = 5 then 1 else 0)
    (hH0 : ∀ i, H i 0 = if i = 0 then 1 else 0)
    (hH5 : ∀ j, H 5 j = if j = 5 then 1 else 0)
    (hmid : midBlock G * midBlock H = 1) :
    (∀ i, (G * H) i 0 = if i = 0 then 1 else 0) ∧
      (∀ j, (G * H) 5 j = if j = 5 then 1 else 0) ∧ midBlock (G * H) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin 6)]
    · rw [hH0 0, if_pos rfl, mul_one]; exact hG0 i
    · intro k _ hk; rw [hH0 k, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ 0) h
  · intro j
    rw [Matrix.mul_apply, Finset.sum_eq_single (5 : Fin 6)]
    · rw [hG5 5, if_pos rfl, one_mul]; exact hH5 j
    · intro k _ hk; rw [hG5 k, if_neg hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ 5) h
  · rw [midBlock_mul_of_left G H hG0 hH5, hmid]

private theorem comm_elem_stdTransvection (i j : Fin 6) (hij : i ≠ j)
    (hi1 : 1 ≤ i.val) (hi4 : i.val ≤ 4) (hj1 : 1 ≤ j.val) (hj4 : j.val ≤ 4) :
    elem i j * CFSG.Holt.SL6.stdTransvection =
      CFSG.Holt.SL6.stdTransvection * elem i j := by
  have hi5 : i ≠ 5 := by intro h; subst h; simp at hi4
  have hj0 : j ≠ 0 := by intro h; subst h; simp at hj1
  fin_cases i <;> fin_cases j <;>
    (first | exact absurd rfl hij | exact absurd rfl hi5 | exact absurd rfl hj0 |
      (apply Subtype.ext; ext a b; fin_cases a <;> fin_cases b <;> decide))

private theorem Jgrp_le_centralizer_t1 :
    Jgrp ≤ Subgroup.centralizer ({CFSG.Holt.SL6.stdTransvection} : Set SL(6, ZMod 2)) := by
  unfold Jgrp
  rw [Subgroup.closure_le]
  rintro g ⟨i, j, hij, hi1, hi4, hj1, hj4, rfl⟩
  change elem i j ∈ Subgroup.centralizer ({CFSG.Holt.SL6.stdTransvection} : Set SL(6, ZMod 2))
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact (comm_elem_stdTransvection i j hij hi1 hi4 hj1 hj4).symm

private theorem Jgrp_le_normalizer_Sone : Jgrp ≤ Subgroup.normalizer Sone := by
  unfold Jgrp Sone
  rw [Subgroup.closure_le]
  rintro g ⟨i, j, hij, hi1, hi4, hj1, hj4, rfl⟩
  apply mem_normalizer_closure_of_conj
  rintro x ⟨k, hk1, rfl⟩
  have hi0 : i ≠ 0 := by intro h; subst h; simp at hi1
  have hj0 : j ≠ 0 := by intro h; subst h; simp at hj1
  have hk0 : k ≠ 0 := by intro h; subst h; simp at hk1
  by_cases hki : k = i
  · rw [hki, elem_conj_zero_eq i j hij hi0 hj0]
    exact mul_mem (Subgroup.subset_closure ⟨i, hi1, rfl⟩) (Subgroup.subset_closure ⟨j, hj1, rfl⟩)
  · rw [elem_conj_zero_ne i j k hij hi0 hj0 hk0 hki]
    exact Subgroup.subset_closure ⟨k, hk1, rfl⟩

private theorem Jgrp_le_normalizer_Ssix : Jgrp ≤ Subgroup.normalizer Ssix := by
  unfold Jgrp Ssix
  rw [Subgroup.closure_le]
  rintro g ⟨i, j, hij, hi1, hi4, hj1, hj4, rfl⟩
  apply mem_normalizer_closure_of_conj
  rintro x ⟨k, hk4, rfl⟩
  have hi5 : i ≠ 5 := by intro h; subst h; simp at hi4
  have hj5 : j ≠ 5 := by intro h; subst h; simp at hj4
  have hk5 : k ≠ 5 := by intro h; subst h; simp at hk4
  by_cases hkj : k = j
  · rw [hkj, elem_conj_five_eq i j hij hi5 hj5]
    exact mul_mem (Subgroup.subset_closure ⟨j, hj4, rfl⟩) (Subgroup.subset_closure ⟨i, hi4, rfl⟩)
  · rw [elem_conj_five_ne i j k hij hi5 hj5 hk5 hkj]
    exact Subgroup.subset_closure ⟨k, hk4, rfl⟩

theorem comm_stdTransvection_of_mem_Jgrp (g : SL(6, ZMod 2)) (hg : g ∈ Jgrp) :
    g * CFSG.Holt.SL6.stdTransvection = CFSG.Holt.SL6.stdTransvection * g := by
  have h : g ∈ Subgroup.centralizer ({CFSG.Holt.SL6.stdTransvection} : Set SL(6, ZMod 2)) :=
    Jgrp_le_centralizer_t1 hg
  rw [Subgroup.mem_centralizer_iff] at h
  exact (h _ (by simp)).symm

private theorem Jgrp_le_normalizer_Sgrp : Jgrp ≤ Subgroup.normalizer Sgrp := by
  intro j hj
  exact Subgroup.inf_normalizer_le_normalizer_sup Sone Ssix
    ⟨Jgrp_le_normalizer_Sone hj, Jgrp_le_normalizer_Ssix hj⟩

theorem conj_mem_Sgrp_of_mem_Jgrp (j x : SL(6, ZMod 2)) (hj : j ∈ Jgrp) (hx : x ∈ Sgrp) :
    j * x * j⁻¹ ∈ Sgrp :=
  (Subgroup.le_normalizer_iff.mp Jgrp_le_normalizer_Sgrp) j hj x hx

theorem mem_Sgrp_sup_Jgrp_iff (g : SL(6, ZMod 2)) :
    g ∈ Sgrp ⊔ Jgrp ↔ ∃ s ∈ Sgrp, ∃ j ∈ Jgrp, g = s * j := by
  have hnorm : Jgrp ≤ Subgroup.normalizer Sgrp := Jgrp_le_normalizer_Sgrp
  have hcoe : (↑(Sgrp ⊔ Jgrp) : Set SL(6, ZMod 2)) =
      (Sgrp : Set SL(6, ZMod 2)) * (Jgrp : Set SL(6, ZMod 2)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Sgrp Jgrp hnorm
  constructor
  · intro hg
    change g ∈ (↑(Sgrp ⊔ Jgrp) : Set SL(6, ZMod 2)) at hg
    rw [hcoe] at hg
    rw [Set.mem_mul] at hg
    obtain ⟨s, hs, j, hj, hsj⟩ := hg
    exact ⟨s, hs, j, hj, hsj.symm⟩
  · rintro ⟨s, hs, j, hj, rfl⟩
    change s * j ∈ (↑(Sgrp ⊔ Jgrp) : Set SL(6, ZMod 2))
    rw [hcoe]
    exact Set.mul_mem_mul hs hj

theorem centralizer_stdTransvection_eq :
    Subgroup.centralizer ({CFSG.Holt.SL6.stdTransvection} : Set SL(6, ZMod 2)) = Sgrp ⊔ Jgrp := by
  apply le_antisymm
  · intro g hg
    have hcomm : CFSG.Holt.SL6.stdTransvection * g = g * CFSG.Holt.SL6.stdTransvection :=
      Subgroup.mem_centralizer_iff.mp hg CFSG.Holt.SL6.stdTransvection (by simp)
    have hmat : (1 + Matrix.single (0 : Fin 6) (5 : Fin 6) (1 : ZMod 2)) * g.1 =
        g.1 * (1 + Matrix.single (0 : Fin 6) (5 : Fin 6) 1) := by
      have := congrArg (fun x : SL(6, ZMod 2) => (x : Matrix (Fin 6) (Fin 6) (ZMod 2))) hcomm
      simpa [CFSG.Holt.SL6.coe_stdTransvection] using this
    have hE : Matrix.single (0 : Fin 6) (5 : Fin 6) (1 : ZMod 2) * g.1 =
        g.1 * Matrix.single (0 : Fin 6) (5 : Fin 6) 1 := by
      have h := hmat
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one] at h
      exact add_left_cancel h
    have hcommE : Commute (Matrix.single (0 : Fin 6) (5 : Fin 6) (1 : ZMod 2)) g.1 := hE
    have hcol : ∀ i, i ≠ 0 → g.1 i 0 = 0 :=
      fun i hi => Matrix.col_eq_zero_of_commute_single hcommE hi
    have hrow : ∀ j, j ≠ 5 → g.1 5 j = 0 :=
      fun j hj => Matrix.row_eq_zero_of_commute_single hcommE hj
    have hdiag : g.1 5 5 = g.1 0 0 := by
      have h := congrFun (congrFun hE 0) 5
      simpa [Matrix.single_mul_apply_same, Matrix.mul_single_apply_same] using h
    have hfirst : ∀ i, g.1 i 0 = if i = 0 then g.1 0 0 else 0 := by
      intro i; by_cases hi : i = 0
      · subst hi; simp
      · rw [hcol i hi]; simp [hi]
    have hdet1 := det_of_firstcol g.1 (g.1 0 0) hfirst
    have hl_ne : g.1 0 0 ≠ 0 := by
      intro h0
      have : g.1.det = 0 := by rw [hdet1, h0, zero_mul]
      rw [g.2] at this
      exact one_ne_zero this
    have hl : g.1 0 0 = 1 := by
      rcases zmod2_eq_zero_or_one (g.1 0 0) with h | h
      · exact absurd h hl_ne
      · exact h
    have hG0 : ∀ i, g.1 i 0 = if i = 0 then 1 else 0 := by
      intro i; rw [hfirst i, hl]
    have hG5 : ∀ j, g.1 5 j = if j = 5 then 1 else 0 := by
      intro j; by_cases hj : j = 5
      · subst hj; simp [hdiag, hl]
      · rw [hrow j hj]; simp [hj]
    have hA0 : (midBlock g.1).det = 1 := by
      have h := det_of_firstcol_lastrow g.1 1 hG0 hG5
      rw [one_mul, one_mul] at h
      rw [← h]
      exact g.2
    let j0 : SL(6, ZMod 2) := embSL ⟨midBlock g.1, hA0⟩
    have hj0 : j0 ∈ Jgrp := range_embSL_le_Jgrp ⟨⟨midBlock g.1, hA0⟩, rfl⟩
    let H : SL(6, ZMod 2) := j0⁻¹
    have hHmem : H ∈ Jgrp := by
      change j0⁻¹ ∈ Jgrp
      exact Subgroup.inv_mem _ hj0
    have hHshape := (mem_Jgrp_iff H).mp hHmem
    have hH0 : ∀ i, H.1 i 0 = if i = 0 then 1 else 0 := by
      intro i; by_cases hi : i = 0
      · subst hi; simpa using hHshape.1
      · rw [hHshape.2.2.1 i hi]; simp [hi]
    have hH5 : ∀ j, H.1 5 j = if j = 5 then 1 else 0 := by
      intro j; by_cases hj : j = 5
      · subst hj; simpa using hHshape.2.1
      · rw [hHshape.2.2.2.2.2 j hj]; simp [hj]
    have hmidj : midBlock g.1 * midBlock H.1 = 1 := by
      have hm := midBlock_mul_of_left (j0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) H.1
        (emb_first_col (midBlock g.1)) hH5
      rw [show (j0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) * H.1 = 1 from by
            rw [← Matrix.SpecialLinearGroup.coe_mul]
            exact congrArg Subtype.val (mul_inv_cancel j0),
          midBlock_one,
          show midBlock (j0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = midBlock g.1 from by
            rw [show (j0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = emb (midBlock g.1) from rfl,
              midBlock_emb]] at hm
      exact hm.symm
    have hshape := mul_shape_of_shapes g.1 H.1 hG0 hG5 hH0 hH5 hmidj
    have hs : g * H ∈ Sgrp := by
      rw [mem_Sgrp_iff]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [Matrix.SpecialLinearGroup.coe_mul] using hshape.1 0
      · simpa [Matrix.SpecialLinearGroup.coe_mul] using hshape.2.1 5
      · intro i j hi1 hi4 hj1 hj4
        have hm : (g.1 * H.1) i j = if i = j then 1 else 0 := by
          have h := congrFun (congrFun hshape.2.2 ⟨i.val - 1, by omega⟩) ⟨j.val - 1, by omega⟩
          rw [midBlock, Matrix.submatrix_apply] at h
          rw [embIdx_pred hi1 hi4, embIdx_pred hj1 hj4] at h
          rw [Matrix.one_apply] at h
          by_cases hij : i = j
          · have hab : (⟨i.val - 1, by omega⟩ : Fin 4) = ⟨j.val - 1, by omega⟩ := by
              subst hij; rfl
            rw [if_pos hab] at h; rw [if_pos hij]; exact h
          · have hab : (⟨i.val - 1, by omega⟩ : Fin 4) ≠ ⟨j.val - 1, by omega⟩ := by
              intro hh; exact hij (Fin.ext (by have := congrArg Fin.val hh; simp at this; omega))
            rw [if_neg hab] at h; rw [if_neg hij]; exact h
        simpa [Matrix.SpecialLinearGroup.coe_mul] using hm
      · intro i hi
        simpa [Matrix.SpecialLinearGroup.coe_mul, if_neg hi] using hshape.1 i
      · intro j hj
        simpa [Matrix.SpecialLinearGroup.coe_mul, if_neg hj] using hshape.2.1 j
    have hg_eq : g = (g * H) * j0 := by
      rw [show H = j0⁻¹ from rfl, mul_assoc, inv_mul_cancel, mul_one]
    rw [hg_eq]
    exact Subgroup.mul_mem_sup hs hj0
  · refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (comm_stdTransvection_of_mem_Sgrp x hx).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (comm_stdTransvection_of_mem_Jgrp x hx).symm
end CFSG.StandardType.FF81.CentE6
