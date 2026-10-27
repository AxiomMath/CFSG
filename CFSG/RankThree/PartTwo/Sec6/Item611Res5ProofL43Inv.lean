module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofL43Cent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434RemL43

abbrev V4 : Type := Fin 4 → ZMod 3

@[expose] def colMat (c₀ c₁ c₂ c₃ : V4) : Mat4 := Matrix.of fun i k => ![c₀, c₁, c₂, c₃] k i

theorem colMat_mulVec (c₀ c₁ c₂ c₃ x : V4) :
    colMat c₀ c₁ c₂ c₃ *ᵥ x = x 0 • c₀ + x 1 • c₁ + x 2 • c₂ + x 3 • c₃ := by
  ext i
  simp [colMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem mul_colMat (T : Mat4) (c₀ c₁ c₂ c₃ : V4) :
    T * colMat c₀ c₁ c₂ c₃ = colMat (T *ᵥ c₀) (T *ᵥ c₁) (T *ᵥ c₂) (T *ᵥ c₃) := by
  ext i k
  fin_cases k <;> simp [colMat, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem colMat_mul_jMat (c₀ c₁ c₂ c₃ : V4) :
    colMat c₀ c₁ c₂ c₃ * jMat = colMat c₁ ((2 : ZMod 3) • c₀) c₃ ((2 : ZMod 3) • c₂) := by
  ext i k
  fin_cases k <;> simp [colMat, jMat, Matrix.mul_apply, Fin.sum_univ_four, mul_comm]

theorem colMat_mul_dMat (c₀ c₁ c₂ c₃ : V4) :
    colMat c₀ c₁ c₂ c₃ * dMat = colMat c₀ c₁ ((2 : ZMod 3) • c₂) ((2 : ZMod 3) • c₃) := by
  ext i k
  fin_cases k <;> simp [colMat, dMat, Matrix.mul_apply, Fin.sum_univ_four, mul_comm]

theorem exists_conj_of_colMat {T R : Mat4} {c₀ c₁ c₂ c₃ : V4}
    (hind : ∀ x : V4, x 0 • c₀ + x 1 • c₁ + x 2 • c₂ + x 3 • c₃ = 0 → x = 0)
    (hTR : T * colMat c₀ c₁ c₂ c₃ = colMat c₀ c₁ c₂ c₃ * R) :
    ∃ g h : Mat4, g * h = 1 ∧ g * T = R * g := by
  set Q := colMat c₀ c₁ c₂ c₃
  have hdet : IsUnit Q.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [colMat_mulVec] at hx
    exact hx0 (hind x hx)
  refine ⟨Q⁻¹, Q, Matrix.nonsing_inv_mul Q hdet, ?_⟩
  calc Q⁻¹ * T = Q⁻¹ * T * (Q * Q⁻¹) := by rw [Matrix.mul_nonsing_inv Q hdet, Matrix.mul_one]
    _ = Q⁻¹ * (T * Q) * Q⁻¹ := by simp only [Matrix.mul_assoc]
    _ = Q⁻¹ * (Q * R) * Q⁻¹ := by rw [hTR]
    _ = (Q⁻¹ * Q) * R * Q⁻¹ := by simp only [Matrix.mul_assoc]
    _ = R * Q⁻¹ := by rw [Matrix.nonsing_inv_mul Q hdet, Matrix.one_mul]

theorem eq_zero_of_sq_add_sq {c d : ZMod 3} (h : c ^ 2 + d ^ 2 = 0) : c = 0 ∧ d = 0 := by
  revert c d
  decide

theorem mulVec_mulVec_of_sq_eq_neg_one {T : Mat4} (hT : T * T = -1) (x : V4) :
    T *ᵥ (T *ᵥ x) = -x := by
  rw [Matrix.mulVec_mulVec, hT, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem indep_of_sq_eq_neg_one {T : Mat4} (hT : T * T = -1) {v w : V4} (hv : v ≠ 0)
    (hw : ∀ a b : ZMod 3, w ≠ a • v + b • (T *ᵥ v)) (x : V4)
    (hx : x 0 • v + x 1 • (T *ᵥ v) + x 2 • w + x 3 • (T *ᵥ w) = 0) : x = 0 := by
  have hT2 := mulVec_mulVec_of_sq_eq_neg_one hT
  have hTx : x 0 • (T *ᵥ v) - x 1 • v + x 2 • (T *ᵥ w) - x 3 • w = 0 := by
    have h := congrArg (fun y => T *ᵥ y) hx
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hT2, Matrix.mulVec_zero] at h
    rw [← h]
    module
  have hc : ∀ i, x 0 • v i + x 1 • (T *ᵥ v) i + x 2 • w i + x 3 • (T *ᵥ w) i = 0 :=
    fun i => by simpa using congrFun hx i
  have hTc : ∀ i, x 0 • (T *ᵥ v) i - x 1 • v i + x 2 • (T *ᵥ w) i - x 3 • w i = 0 :=
    fun i => by simpa using congrFun hTx i
  have h23 : x 2 ^ 2 + x 3 ^ 2 = 0 := by
    by_contra hne
    apply hw (-(x 2 * x 0 + x 3 * x 1) / (x 2 ^ 2 + x 3 ^ 2))
      (-(x 2 * x 1 - x 3 * x 0) / (x 2 ^ 2 + x 3 ^ 2))
    ext i
    have h1 := hc i
    have h2 := hTc i
    simp only [smul_eq_mul] at h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination x 2 * h1 - x 3 * h2
  obtain ⟨hx2, hx3⟩ := eq_zero_of_sq_add_sq h23
  have h01 : x 0 ^ 2 + x 1 ^ 2 = 0 := by
    by_contra hne
    apply hv
    ext i
    have h1 := hc i
    have h2 := hTc i
    simp only [smul_eq_mul, hx2, hx3, zero_mul, add_zero] at h1 h2
    have h3 : (x 0 ^ 2 + x 1 ^ 2) * v i = 0 := by linear_combination x 0 * h1 - x 1 * h2
    simpa [hne] using h3
  obtain ⟨hx0, hx1⟩ := eq_zero_of_sq_add_sq h01
  ext i
  fin_cases i
  · exact hx0
  · exact hx1
  · exact hx2
  · exact hx3

@[expose] def eVec (k : Fin 4) : V4 := fun i => if i = k then 1 else 0

theorem not_mem_span_of_mem_span {T : Mat4} {a b : ZMod 3}
    (h : eVec 1 = a • eVec 0 + b • (T *ᵥ eVec 0)) (a' b' : ZMod 3) :
    eVec 2 ≠ a' • eVec 0 + b' • (T *ᵥ eVec 0) := by
  intro h'
  generalize T *ᵥ eVec 0 = t at h h'
  have h1 : (1 : ZMod 3) = a * 0 + b * t 1 := by simpa [eVec] using congrFun h 1
  have h2 : (0 : ZMod 3) = a * 0 + b * t 2 := by simpa [eVec] using congrFun h 2
  have h2' : (1 : ZMod 3) = a' * 0 + b' * t 2 := by simpa [eVec] using congrFun h' 2
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h1
  have ht : t 2 = 0 := by
    have h3 : b * t 2 = 0 := by linear_combination -h2
    exact (mul_eq_zero.mp h3).resolve_left hb
  rw [ht] at h2'
  simp at h2'

theorem exists_conj_jMat {T : Mat4} (hT : T * T = -1) :
    ∃ g h : Mat4, g * h = 1 ∧ g * T = jMat * g := by
  have hv : eVec 0 ≠ 0 := fun h => by simpa [eVec] using congrFun h 0
  obtain ⟨w, hw⟩ : ∃ w : V4, ∀ a b : ZMod 3, w ≠ a • eVec 0 + b • (T *ᵥ eVec 0) := by
    by_cases h : ∃ a b : ZMod 3, eVec 1 = a • eVec 0 + b • (T *ᵥ eVec 0)
    · obtain ⟨a, b, h⟩ := h
      exact ⟨eVec 2, not_mem_span_of_mem_span h⟩
    · push Not at h
      exact ⟨eVec 1, h⟩
  refine exists_conj_of_colMat (c₀ := eVec 0) (c₁ := T *ᵥ eVec 0) (c₂ := w) (c₃ := T *ᵥ w)
    (indep_of_sq_eq_neg_one hT hv hw) ?_
  rw [mul_colMat, colMat_mul_jMat, mulVec_mulVec_of_sq_eq_neg_one hT,
    mulVec_mulVec_of_sq_eq_neg_one hT]
  have h2 : ∀ x : V4, -x = (2 : ZMod 3) • x := fun x => by
    ext i
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    generalize x i = y
    revert y
    decide
  rw [h2, h2]

theorem det_eq_two_of_add_one {T : Mat4} (hT : T * T = 1) {v l : V4}
    (hP : ∀ i j, (1 + T) i j = v i * l j) (hne : ∃ i j, v i * l j ≠ 0) : T.det = 2 := by
  have hsq : (1 + T) * (1 + T) = (2 : ZMod 3) • (1 + T) := by
    have h : (1 + T) * (1 + T) = 1 + T + T + T * T := by noncomm_ring
    rw [h, hT]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hdot : l ⬝ᵥ v = 2 := by
    obtain ⟨i, j, hij⟩ := hne
    have h := congrFun (congrFun hsq i) j
    simp only [Matrix.mul_apply, hP, Matrix.smul_apply, smul_eq_mul] at h
    have h' : (v i * l j) * (l ⬝ᵥ v) = (v i * l j) * 2 := by
      rw [mul_comm (v i * l j) 2, ← h, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    exact mul_left_cancel₀ hij h'
  have hneg : -T = 1 + Matrix.replicateCol Unit (-v) * Matrix.replicateRow Unit l := by
    ext i j
    have h := hP i j
    simp only [Matrix.add_apply] at h
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Pi.neg_apply, Finset.univ_unique, Finset.sum_singleton]
    linear_combination -h
  have hdetneg : (-T).det = T.det := by
    rw [Matrix.det_neg, Fintype.card_fin]
    norm_num
  rw [← hdetneg, hneg, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_neg, hdot]
  decide

theorem det_eq_two_of_one_sub {T : Mat4} (hT : T * T = 1) {w m : V4}
    (hM : ∀ i j, (1 - T) i j = w i * m j) (hne : ∃ i j, w i * m j ≠ 0) : T.det = 2 := by
  have hsq : (1 - T) * (1 - T) = (2 : ZMod 3) • (1 - T) := by
    have h : (1 - T) * (1 - T) = 1 - T - T + T * T := by noncomm_ring
    rw [h, hT]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hdot : m ⬝ᵥ w = 2 := by
    obtain ⟨i, j, hij⟩ := hne
    have h := congrFun (congrFun hsq i) j
    simp only [Matrix.mul_apply, hM, Matrix.smul_apply, smul_eq_mul] at h
    have h' : (w i * m j) * (m ⬝ᵥ w) = (w i * m j) * 2 := by
      rw [mul_comm (w i * m j) 2, ← h, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    exact mul_left_cancel₀ hij h'
  have hT' : T = 1 + Matrix.replicateCol Unit (-w) * Matrix.replicateRow Unit m := by
    ext i j
    have h := hM i j
    simp only [Matrix.sub_apply] at h
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Pi.neg_apply, Finset.univ_unique, Finset.sum_singleton]
    linear_combination -h
  rw [hT', Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_neg, hdot]
  decide

@[expose] def colOf (P : Mat4) (j : Fin 4) : V4 := fun i => P i j

theorem rank_one_or_two (P : Mat4) (hP : P ≠ 0) :
    (∃ v l : V4, (∀ i j, P i j = v i * l j) ∧ ∃ i j, v i * l j ≠ 0) ∨
      ∃ j₁ j₂ : Fin 4, colOf P j₁ ≠ 0 ∧ ∀ a : ZMod 3, colOf P j₂ ≠ a • colOf P j₁ := by
  obtain ⟨j₁, hj₁⟩ : ∃ j₁, colOf P j₁ ≠ 0 := by
    by_contra h
    push Not at h
    apply hP
    ext i j
    simpa [colOf] using congrFun (h j) i
  by_cases h : ∃ j₂ : Fin 4, ∀ a : ZMod 3, colOf P j₂ ≠ a • colOf P j₁
  · obtain ⟨j₂, hj₂⟩ := h
    exact Or.inr ⟨j₁, j₂, hj₁, hj₂⟩
  · push Not at h
    choose l hl using h
    left
    refine ⟨colOf P j₁, l, fun i j => ?_, ?_⟩
    · have := congrFun (hl j) i
      simp only [colOf, Pi.smul_apply, smul_eq_mul] at this
      rw [this, mul_comm]
      rfl
    · obtain ⟨i, hi⟩ : ∃ i, colOf P j₁ i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hj₁ (funext hc)
      have hl1 : l j₁ = 1 := by
        have := congrFun (hl j₁) i
        simp only [Pi.smul_apply, smul_eq_mul] at this
        have h1 : (l j₁ - 1) * colOf P j₁ i = 0 := by linear_combination -this
        rcases mul_eq_zero.mp h1 with h1 | h1
        · linear_combination h1
        · exact absurd h1 hi
      exact ⟨i, j₁, by rw [hl1, mul_one]; exact hi⟩

theorem indep_of_sq_eq_one {T : Mat4} {v₁ v₂ w₁ w₂ : V4} (hv₁ : T *ᵥ v₁ = v₁)
    (hv₂ : T *ᵥ v₂ = v₂) (hw₁ : T *ᵥ w₁ = -w₁) (hw₂ : T *ᵥ w₂ = -w₂) (hv₁0 : v₁ ≠ 0)
    (hw₁0 : w₁ ≠ 0) (hv : ∀ a : ZMod 3, v₂ ≠ a • v₁) (hw : ∀ a : ZMod 3, w₂ ≠ a • w₁) (x : V4)
    (hx : x 0 • v₁ + x 1 • v₂ + x 2 • w₁ + x 3 • w₂ = 0) : x = 0 := by
  have hTx : x 0 • v₁ + x 1 • v₂ - x 2 • w₁ - x 3 • w₂ = 0 := by
    have h := congrArg (fun y => T *ᵥ y) hx
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hv₁, hv₂, hw₁, hw₂,
      Matrix.mulVec_zero] at h
    rw [← h]
    module
  have hc : ∀ i, x 0 * v₁ i + x 1 * v₂ i + x 2 * w₁ i + x 3 * w₂ i = 0 :=
    fun i => by simpa using congrFun hx i
  have hTc : ∀ i, x 0 * v₁ i + x 1 * v₂ i - x 2 * w₁ i - x 3 * w₂ i = 0 :=
    fun i => by simpa using congrFun hTx i
  have hV : ∀ i, x 0 * v₁ i + x 1 * v₂ i = 0 := fun i => by
    linear_combination 2 * hc i + 2 * hTc i - (x 0 * v₁ i + x 1 * v₂ i) * three_eq_zero
  have hW : ∀ i, x 2 * w₁ i + x 3 * w₂ i = 0 := fun i => by
    linear_combination 2 * hc i - 2 * hTc i - (x 2 * w₁ i + x 3 * w₂ i) * three_eq_zero
  have pair : ∀ {u u' : V4} {c c' : ZMod 3}, u ≠ 0 → (∀ a : ZMod 3, u' ≠ a • u) →
      (∀ i, c * u i + c' * u' i = 0) → c = 0 ∧ c' = 0 := by
    intro u u' c c' hu hu' h
    have hc' : c' = 0 := by
      by_contra hne
      apply hu' (-c / c')
      ext i
      have := h i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination this
    refine ⟨?_, hc'⟩
    by_contra hne
    apply hu
    ext i
    have := h i
    rw [hc', zero_mul, add_zero] at this
    simpa [hne] using this
  obtain ⟨hx0, hx1⟩ := pair hv₁0 hv hV
  obtain ⟨hx2, hx3⟩ := pair hw₁0 hw hW
  ext i
  fin_cases i
  · exact hx0
  · exact hx1
  · exact hx2
  · exact hx3

theorem exists_conj_dMat {T : Mat4} (hT : T * T = 1) (h1 : T ≠ 1) (hm1 : T ≠ -1)
    (hdet : T.det = 1) : ∃ g h : Mat4, g * h = 1 ∧ g * T = dMat * g := by
  have hdet2 : T.det ≠ 2 := by rw [hdet]; decide
  have hTP : T * (1 + T) = 1 + T := by rw [mul_add, hT, Matrix.mul_one, add_comm]
  have hTM : T * (1 - T) = -(1 - T) := by rw [mul_sub, hT, Matrix.mul_one, neg_sub]
  have hcolP : ∀ j, T *ᵥ colOf (1 + T) j = colOf (1 + T) j := fun j => by
    ext i
    have := congrFun (congrFun hTP i) j
    simpa [colOf, Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hcolM : ∀ j, T *ᵥ colOf (1 - T) j = -colOf (1 - T) j := fun j => by
    ext i
    have := congrFun (congrFun hTM i) j
    simpa [colOf, Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hP0 : (1 + T : Mat4) ≠ 0 := fun h => hm1 (by rw [← neg_eq_of_add_eq_zero_right h])
  have hM0 : (1 - T : Mat4) ≠ 0 := fun h => h1 (sub_eq_zero.mp h).symm
  rcases rank_one_or_two (1 + T) hP0 with ⟨v, l, hvl, hne⟩ | ⟨j₁, j₂, hj₁, hj₂⟩
  · exact absurd (det_eq_two_of_add_one hT hvl hne) hdet2
  rcases rank_one_or_two (1 - T) hM0 with ⟨w, m, hwm, hne⟩ | ⟨k₁, k₂, hk₁, hk₂⟩
  · exact absurd (det_eq_two_of_one_sub hT hwm hne) hdet2
  refine exists_conj_of_colMat (c₀ := colOf (1 + T) j₁) (c₁ := colOf (1 + T) j₂)
    (c₂ := colOf (1 - T) k₁) (c₃ := colOf (1 - T) k₂)
    (indep_of_sq_eq_one (hcolP j₁) (hcolP j₂) (hcolM k₁) (hcolM k₂) hj₁ hk₁ hj₂ hk₂) ?_
  rw [mul_colMat, colMat_mul_dMat, hcolP, hcolP, hcolM, hcolM]
  have h2 : ∀ x : V4, -x = (2 : ZMod 3) • x := fun x => by
    ext i
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    generalize x i = y
    revert y
    decide
  rw [h2, h2]

theorem card_centralizer_of_sq {t : SL4} (ht : (t : Mat4) * t = 1 ∨ (t : Mat4) * t = -1)
    (h1 : (t : Mat4) ≠ 1) (hm1 : (t : Mat4) ≠ -1) :
    Nat.card (Subgroup.centralizer ({t} : Set SL4)) = 1152 ∨
      Nat.card (Subgroup.centralizer ({t} : Set SL4)) = 2880 := by
  rcases ht with ht | ht
  · obtain ⟨g, h, hgh, hg⟩ := exists_conj_dMat ht h1 hm1 t.2
    left
    rw [card_centralizer_conj (M' := dSL) hgh hg, card_centralizer_dSL]
  · obtain ⟨g, h, hgh, hg⟩ := exists_conj_jMat ht
    right
    rw [card_centralizer_conj (M' := jSL) hgh hg, card_centralizer_jSL]

end CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43
