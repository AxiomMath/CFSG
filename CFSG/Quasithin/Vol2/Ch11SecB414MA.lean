module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3A

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open Matrix

variable {F : Type} [Field F]

@[expose] def det2 (v w : Fin 2 → F) : F := v 0 * w 1 - v 1 * w 0

theorem det2_mulVec (A : Matrix (Fin 2) (Fin 2) F) (v w : Fin 2 → F) :
    det2 (A *ᵥ v) (A *ᵥ w) = A.det * det2 v w := by
  simp only [det2, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem det2_self (v : Fin 2 → F) : det2 v v = 0 := by
  simp only [det2]
  ring

theorem det2_add_left (u v w : Fin 2 → F) : det2 (u + v) w = det2 u w + det2 v w := by
  simp only [det2, Pi.add_apply]
  ring

theorem det2_add_right (u v w : Fin 2 → F) : det2 u (v + w) = det2 u v + det2 u w := by
  simp only [det2, Pi.add_apply]
  ring

theorem det2_smul_left (c : F) (v w : Fin 2 → F) : det2 (c • v) w = c * det2 v w := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]
  ring

theorem det2_smul_right (c : F) (v w : Fin 2 → F) : det2 v (c • w) = c * det2 v w := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]
  ring

theorem det2_swap (v w : Fin 2 → F) : det2 w v = - det2 v w := by
  simp only [det2]
  ring

theorem ne_zero_of_det2_ne_zero_left {v w : Fin 2 → F} (h : det2 v w ≠ 0) : v ≠ 0 := by
  rintro rfl
  simp [det2] at h

theorem exists_smul_of_det2_eq_zero {v w : Fin 2 → F} (hv : v ≠ 0) (h : det2 v w = 0) :
    ∃ c : F, w = c • v := by
  simp only [det2] at h
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨w 1 / v 1, funext fun i => ?_⟩
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨w 0 / v 0, funext fun i => ?_⟩
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem eq_zero_of_det2 {x y e : Fin 2 → F} (hxy : det2 x y ≠ 0) (hxe : det2 x e = 0)
    (hey : det2 e y = 0) : e = 0 := by
  simp only [det2] at hxy hxe hey
  have h0 : e 0 * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination x 0 * hey + y 0 * hxe
  have h1 : e 1 * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination y 1 * hxe + x 1 * hey
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp h0).resolve_right hxy
  · exact (mul_eq_zero.mp h1).resolve_right hxy

theorem exists_SL2_pair {v w v' w' : Fin 2 → F} (hd : det2 v w ≠ 0)
    (he : det2 v' w' = det2 v w) :
    ∃ A : SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v' ∧ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w' := by
  simp only [det2] at hd he
  obtain ⟨D, hD⟩ : ∃ D : F, v 0 * w 1 - v 1 * w 0 = D := ⟨_, rfl⟩
  rw [hD] at hd he
  let M : Matrix (Fin 2) (Fin 2) F :=
    !![(v' 0 * w 1 - w' 0 * v 1) / D, (w' 0 * v 0 - v' 0 * w 0) / D;
      (v' 1 * w 1 - w' 1 * v 1) / D, (w' 1 * v 0 - v' 1 * w 0) / D]
  have hdet : M.det = 1 := by
    rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination (v 0 * w 1 - v 1 * w 0) * he + D * hD
  refine ⟨⟨M, hdet⟩, ?_, ?_⟩
  · funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fin_cases i
    · simp only [M, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      field_simp
      linear_combination v' 0 * hD
    · simp only [M, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      field_simp
      linear_combination v' 1 * hD
  · funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fin_cases i
    · simp only [M, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      field_simp
      linear_combination w' 0 * hD
    · simp only [M, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      field_simp
      linear_combination w' 1 * hD

@[expose] def e0 : Fin 2 → F := ![1, 0]

theorem exists_SL2_e0 {v : Fin 2 → F} (hv : v ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = v := by
  have h1 : det2 (e0 : Fin 2 → F) ![0, 1] = 1 := by simp [det2, e0]
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 → F, det2 v w = 1 := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
      exact ⟨![-1 / v 1, 0], by simp [det2, h0]; field_simp⟩
    · exact ⟨![0, 1 / v 0], by simp [det2]; field_simp⟩
  obtain ⟨A, hA, -⟩ := exists_SL2_pair (by rw [h1]; exact one_ne_zero) (hw.trans h1.symm)
  exact ⟨A, hA⟩

theorem e0_ne_zero : (e0 : Fin 2 → F) ≠ 0 := fun h => by
  have := congrFun h 0
  simp [e0] at this

theorem coe_mul2 (A B : SpecialLinearGroup (Fin 2) F) :
    ((A * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) := rfl

theorem coe_one2 : ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := rfl

theorem coe_inv_mul (A : SpecialLinearGroup (Fin 2) F) :
    ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← coe_mul2, inv_mul_cancel, coe_one2]

theorem coe_mul_inv (A : SpecialLinearGroup (Fin 2) F) :
    (A : Matrix (Fin 2) (Fin 2) F) *
      ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← coe_mul2, mul_inv_cancel, coe_one2]

theorem inv_mulVec_mulVec (A : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
      ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (A : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    (A : Matrix (Fin 2) (Fin 2) F) *ᵥ
      (((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, coe_mul_inv, Matrix.one_mulVec]

theorem mulVec_ne_zero (A : SpecialLinearGroup (Fin 2) F) {v : Fin 2 → F} (hv : v ≠ 0) :
    (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ≠ 0 := fun h => hv <| by
  rw [← inv_mulVec_mulVec A v, h, Matrix.mulVec_zero]

section Intertwine

variable (ψ : SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F) (w₀ : Fin 2 → F)

@[expose] noncomputable def tMap (v : Fin 2 → F) : Fin 2 → F := by
  classical
  exact if h : v = 0 then 0 else
    ((ψ (exists_SL2_e0 h).choose : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀

variable {ψ w₀}

abbrev StabHyp (ψ : SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F)
    (w₀ : Fin 2 → F) : Prop :=
  ∀ A : SpecialLinearGroup (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0 ↔
    ((ψ A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀ = w₀

theorem tMap_zero : tMap ψ w₀ 0 = 0 := dite_eq_left rfl

theorem tMap_eq (hw : StabHyp ψ w₀) (A : SpecialLinearGroup (Fin 2) F) :
    tMap ψ w₀ ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0) =
      ((ψ A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀ := by
  have hv : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 ≠ 0 := mulVec_ne_zero A e0_ne_zero
  rw [tMap, dite_eq_right hv]
  set B := (exists_SL2_e0 hv).choose with hB
  have hBe : (B : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 :=
    (exists_SL2_e0 hv).choose_spec
  have h1 : ((B⁻¹ * A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0 := by
    rw [coe_mul2, ← Matrix.mulVec_mulVec, ← hBe, inv_mulVec_mulVec]
  have h2 := (hw _).mp h1
  rw [map_mul, map_inv, coe_mul2, ← Matrix.mulVec_mulVec] at h2
  calc ((ψ B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀
      = ((ψ B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
          ((((ψ B)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
            (((ψ A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀)) := by
        rw [h2]
    _ = ((ψ A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀ :=
        mulVec_inv_mulVec _ _

theorem tMap_mulVec (hw : StabHyp ψ w₀) (A : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    tMap ψ w₀ ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
      ((ψ A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ tMap ψ w₀ v := by
  by_cases hv : v = 0
  · subst hv
    rw [Matrix.mulVec_zero, tMap_zero, Matrix.mulVec_zero]
  · obtain ⟨B, rfl⟩ := exists_SL2_e0 hv
    rw [Matrix.mulVec_mulVec, ← coe_mul2, tMap_eq hw, tMap_eq hw, map_mul,
      coe_mul2, Matrix.mulVec_mulVec]

theorem tMap_ne_zero (hw : StabHyp ψ w₀) (hw0 : w₀ ≠ 0) {v : Fin 2 → F} (hv : v ≠ 0) :
    tMap ψ w₀ v ≠ 0 := by
  obtain ⟨B, rfl⟩ := exists_SL2_e0 hv
  rw [tMap_eq hw]
  exact mulVec_ne_zero _ hw0

theorem tMap_injective (hw : StabHyp ψ w₀) (hw0 : w₀ ≠ 0) : Function.Injective (tMap ψ w₀) := by
  intro v v' h
  by_cases hv : v = 0
  · subst hv
    by_contra hv'
    exact tMap_ne_zero hw hw0 (Ne.symm hv') (h.symm.trans tMap_zero)
  by_cases hv' : v' = 0
  · subst hv'
    exact absurd (h.trans tMap_zero) (tMap_ne_zero hw hw0 hv)
  obtain ⟨A, rfl⟩ := exists_SL2_e0 hv
  obtain ⟨A', rfl⟩ := exists_SL2_e0 hv'
  rw [tMap_eq hw, tMap_eq hw] at h
  have h1 : ((ψ (A⁻¹ * A') : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w₀ =
      w₀ := by
    rw [map_mul, map_inv, coe_mul2, ← Matrix.mulVec_mulVec, ← h,
      inv_mulVec_mulVec]
  have h2 := (hw _).mpr h1
  rw [coe_mul2, ← Matrix.mulVec_mulVec] at h2
  calc (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0
      = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *ᵥ ((A' : Matrix (Fin 2) (Fin 2) F) *ᵥ e0)) := by rw [h2]
    _ = (A' : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 := mulVec_inv_mulVec _ _

theorem det2_tMap_eq (hw : StabHyp ψ w₀) {v w v' w' : Fin 2 → F} (hd : det2 v w ≠ 0)
    (he : det2 v' w' = det2 v w) :
    det2 (tMap ψ w₀ v') (tMap ψ w₀ w') = det2 (tMap ψ w₀ v) (tMap ψ w₀ w) := by
  obtain ⟨A, rfl, rfl⟩ := exists_SL2_pair hd he
  rw [tMap_mulVec hw, tMap_mulVec hw, det2_mulVec, (ψ A).prop, one_mul]

theorem det2_tMap_ne_zero (hw : StabHyp ψ w₀) (hw0 : w₀ ≠ 0) {v w : Fin 2 → F}
    (hd : det2 v w ≠ 0) : det2 (tMap ψ w₀ v) (tMap ψ w₀ w) ≠ 0 := by
  intro h0
  have hv := ne_zero_of_det2_ne_zero_left hd
  obtain ⟨c, hc⟩ := exists_smul_of_det2_eq_zero (tMap_ne_zero hw hw0 hv) h0
  have he : det2 v (w + v) = det2 v w := by rw [det2_add_right, det2_self, add_zero]
  obtain ⟨A, hAv, hAw⟩ := exists_SL2_pair hd he
  have h1 : tMap ψ w₀ (w + v) = tMap ψ w₀ w := by
    rw [← hAw, tMap_mulVec hw, hc, Matrix.mulVec_smul, ← tMap_mulVec hw, hAv]
  have h2 := tMap_injective hw hw0 h1
  apply hv
  have := congrArg (fun u => u - w) h2
  simpa using this

theorem tMap_add_of_det2 (hw : StabHyp ψ w₀) (hw0 : w₀ ≠ 0) {v w : Fin 2 → F}
    (hd : det2 v w ≠ 0) : tMap ψ w₀ (v + w) = tMap ψ w₀ v + tMap ψ w₀ w := by
  have h1 : det2 v (v + w) = det2 v w := by rw [det2_add_right, det2_self, zero_add]
  have h2 : det2 (v + w) w = det2 v w := by rw [det2_add_left, det2_self, add_zero]
  have e1 := det2_tMap_eq hw hd h1
  have e2 := det2_tMap_eq hw hd h2
  have hxy := det2_tMap_ne_zero hw hw0 hd
  set x := tMap ψ w₀ v
  set y := tMap ψ w₀ w
  set z := tMap ψ w₀ (v + w)
  have h0 : z - x - y = 0 := by
    refine eq_zero_of_det2 hxy ?_ ?_
    · rw [sub_eq_add_neg, sub_eq_add_neg, det2_add_right, det2_add_right, ← neg_one_smul F x,
        ← neg_one_smul F y, det2_smul_right, det2_smul_right, det2_self, e1]
      ring
    · rw [sub_eq_add_neg, sub_eq_add_neg, det2_add_left, det2_add_left, ← neg_one_smul F x,
        ← neg_one_smul F y, det2_smul_left, det2_smul_left, det2_self, e2]
      ring
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

theorem exists_det2_ne_zero {v : Fin 2 → F} (hv : v ≠ 0) : ∃ u : Fin 2 → F, det2 v u ≠ 0 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    exact ⟨![1, 0], by simpa [det2] using h1⟩
  · exact ⟨![0, 1], by simpa [det2] using h0⟩

theorem tMap_add [CharP F 2] (hw : StabHyp ψ w₀) (hw0 : w₀ ≠ 0) (v w : Fin 2 → F) :
    tMap ψ w₀ (v + w) = tMap ψ w₀ v + tMap ψ w₀ w := by
  have h2 : ∀ u : Fin 2 → F, u + u = 0 := fun u => funext fun i => CharTwo.add_self_eq_zero (u i)
  by_cases hv : v = 0
  · subst hv
    rw [zero_add, tMap_zero, zero_add]
  by_cases hw' : w = 0
  · subst hw'
    rw [add_zero, tMap_zero, add_zero]
  by_cases hd : det2 v w = 0
  · by_cases hvw : v + w = 0
    · have hwv : w = v := by
        have := congrArg (fun u => u + v) hvw
        simp only [zero_add] at this
        rw [add_comm, ← add_assoc, h2, zero_add] at this
        exact this
      rw [hvw, tMap_zero, hwv, h2]
    obtain ⟨u, hu⟩ := exists_det2_ne_zero hv
    obtain ⟨c, rfl⟩ := exists_smul_of_det2_eq_zero hv hd
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hw' (zero_smul F v)
    have hwu : det2 (c • v) u ≠ 0 := by
      rw [det2_smul_left]
      exact mul_ne_zero hc0 hu
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [one_smul] at hvw
      exact hvw (h2 v)
    have hvu : det2 (v + u) (c • v + u) ≠ 0 := by
      have e : det2 (v + u) (c • v + u) = (1 - c) * det2 v u := by
        rw [det2_add_left, det2_add_right, det2_add_right, det2_smul_right, det2_self,
          det2_smul_right, det2_self, det2_swap u v]
        ring
      rw [e]
      exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hc1)) hu
    have e : v + c • v = (v + u) + (c • v + u) := by
      rw [add_add_add_comm, h2, add_zero]
    rw [e, tMap_add_of_det2 hw hw0 hvu, tMap_add_of_det2 hw hw0 hu,
      tMap_add_of_det2 hw hw0 hwu, add_add_add_comm, h2, add_zero]
  · exact tMap_add_of_det2 hw hw0 hd

end Intertwine

@[expose] def stab0 (F : Type) [Field F] : Subgroup (SpecialLinearGroup (Fin 2) F) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0}
  one_mem' := by
    show ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0
    rw [coe_one2, Matrix.one_mulVec]
  mul_mem' {A B} hA hB := by
    show ((A * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0
    rw [coe_mul2, ← Matrix.mulVec_mulVec, hB, hA]
  inv_mem' {A} hA := by
    show ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0
    have hA' : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0 := hA
    conv_lhs => rw [← hA']
    exact inv_mulVec_mulVec A e0

theorem mem_stab0_iff {A : SpecialLinearGroup (Fin 2) F} :
    A ∈ stab0 F ↔ (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧
      (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  show (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0 ↔ _
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, mul_zero, add_zero, Fin.isValue] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]

@[expose] def unip (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem card_stab0 : Nat.card (stab0 F) = Nat.card F := by
  symm
  refine Nat.card_eq_of_bijective (fun t => (⟨unip t, mem_stab0_iff.mpr ⟨rfl, rfl⟩⟩ :
    stab0 F)) ⟨fun s t h => ?_, fun A => ?_⟩
  · have := congrArg (fun A : stab0 F =>
      ((A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simpa [unip] using this
  · obtain ⟨A, hA⟩ := A
    obtain ⟨h0, h1⟩ := mem_stab0_iff.mp hA
    have hdet := A.prop
    rw [Matrix.det_fin_two, h0, h1, one_mul, mul_zero, sub_zero] at hdet
    refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 1, Subtype.ext (Subtype.ext ?_)⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unip, h0, h1, hdet]

theorem exists_stabHyp [Finite F] (hF : Nat.card F = 4)
    (ψ : SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F) :
    ∃ w₀ : Fin 2 → F, w₀ ≠ 0 ∧ StabHyp ψ w₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h60 : Nat.card (SpecialLinearGroup (Fin 2) F) = 60 :=
    CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.card_SL2_four hF
  have hc1 : Nat.card (stab0 F) = 4 := by rw [card_stab0, hF]
  have hc2 : Nat.card ((stab0 F).map ψ.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hc1]
  have hidx : ∀ H : Subgroup (SpecialLinearGroup (Fin 2) F), Nat.card H = 4 → ¬ 2 ∣ H.index := by
    intro H hH h2
    have := H.index_mul_card
    rw [hH, h60] at this
    omega
  let P₁ : Sylow 2 (SpecialLinearGroup (Fin 2) F) :=
    (IsPGroup.of_card (n := 2) (by rw [hc1]; norm_num)).toSylow (hidx _ hc1)
  let P₂ : Sylow 2 (SpecialLinearGroup (Fin 2) F) :=
    (IsPGroup.of_card (n := 2) (by rw [hc2]; norm_num)).toSylow (hidx _ hc2)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) F) P₁ P₂
  have h := congrArg (fun T : Sylow 2 (SpecialLinearGroup (Fin 2) F) =>
    (T : Subgroup (SpecialLinearGroup (Fin 2) F))) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  change (stab0 F).map (MulDistribMulAction.toMonoidEnd (MulAut (SpecialLinearGroup (Fin 2) F))
    (SpecialLinearGroup (Fin 2) F) (MulAut.conj g)) = (stab0 F).map ψ.toMonoidHom at h
  refine ⟨(g : Matrix (Fin 2) (Fin 2) F) *ᵥ e0, mulVec_ne_zero g e0_ne_zero, fun A => ?_⟩
  have hmem : ψ A ∈ (stab0 F).map ψ.toMonoidHom ↔ A ∈ stab0 F :=
    ⟨fun ⟨B, hB, hBA⟩ => ψ.injective hBA ▸ hB, fun hA => ⟨A, hA, rfl⟩⟩
  rw [← h] at hmem
  have hconj : ∀ B : SpecialLinearGroup (Fin 2) F, B ∈ (stab0 F).map
      (MulDistribMulAction.toMonoidEnd (MulAut (SpecialLinearGroup (Fin 2) F))
        (SpecialLinearGroup (Fin 2) F) (MulAut.conj g)) ↔ g⁻¹ * B * g ∈ stab0 F := by
    intro B
    constructor
    · rintro ⟨C, hC, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hC
    · intro hB
      exact ⟨g⁻¹ * B * g, hB, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [hconj] at hmem
  show (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0 ↔ _
  rw [← show A ∈ stab0 F ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0 from Iff.rfl, ← hmem]
  show ((g⁻¹ * ψ A * g : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 = e0 ↔ _
  rw [coe_mul2, coe_mul2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h1
    calc ((ψ A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
          ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ e0)
        = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) *ᵥ (((ψ A : SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) *ᵥ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ e0))) :=
          (mulVec_inv_mulVec g _).symm
      _ = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ e0 := by rw [h1]
  · intro h1
    rw [h1, inv_mulVec_mulVec]

theorem exists_addEquiv_intertwine [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (ψ : SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F) :
    ∃ T : (Fin 2 → F) ≃+ (Fin 2 → F), ∀ (A : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      T ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        ((ψ A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T v := by
  obtain ⟨w₀, hw0, hw⟩ := exists_stabHyp hF ψ
  have hinj := tMap_injective hw hw0
  have hbij : Function.Bijective (tMap ψ w₀) := ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  let T : (Fin 2 → F) ≃+ (Fin 2 → F) :=
    { Equiv.ofBijective _ hbij with map_add' := tMap_add hw hw0 }
  exact ⟨T, fun A v => tMap_mulVec hw A v⟩

end CFSG.Quasithin.H13.Ch4.B414.M
