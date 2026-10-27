module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Quasithin.H13.SL2Two

open Matrix

variable {F : Type*} [Field F]

@[expose] def upperU (x : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, x; 0, 1], by simp [det_fin_two]⟩

@[expose] def diagT (l : F) (hl : l ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![l, 0; 0, l⁻¹], by simp [det_fin_two, hl]⟩

@[expose] def upperB (c d : F) (hc : c ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![c, d; 0, c⁻¹], by simp [det_fin_two, hc]⟩

theorem coe_upperU (x : F) :
    ((upperU x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

theorem coe_diagT (l : F) (hl : l ≠ 0) :
    ((diagT l hl : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![l, 0; 0, l⁻¹] :=
  rfl

theorem coe_upperB (c d : F) (hc : c ≠ 0) :
    ((upperB c d hc : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![c, d; 0, c⁻¹] := rfl

variable [CharP F 2]

@[expose] def swapW : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two, CharTwo.neg_eq]⟩

omit [CharP F 2] in
theorem coe_swapW' (h : ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)).det = 1) :
    ((⟨!![0, 1; 1, 0], h⟩ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 0] := rfl

theorem coe_swapW : ((swapW : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![0, 1; 1, 0] := rfl

theorem det_eq (g : SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 +
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have h := g.2
  rw [det_fin_two] at h
  rwa [sub_eq_add_neg, CharTwo.neg_eq] at h

theorem eq_upper_mul_swap_mul (g : SpecialLinearGroup (Fin 2) F)
    (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    g = upperU ((g : Matrix (Fin 2) (Fin 2) F) 0 0 / (g : Matrix (Fin 2) (Fin 2) F) 1 0) * swapW *
      upperB ((g : Matrix (Fin 2) (Fin 2) F) 1 0) ((g : Matrix (Fin 2) (Fin 2) F) 1 1) hc := by
  have hd := det_eq g
  have hbc : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 + 1 =
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    have h2 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 + 1 =
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 +
          ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 +
            (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0) := by
      rw [hd]
    rw [h2, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 / (g : Matrix (Fin 2) (Fin 2) F) 1 0 *
      (g : Matrix (Fin 2) (Fin 2) F) 1 1 + ((g : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹ =
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    have : (g : Matrix (Fin 2) (Fin 2) F) 0 0 / (g : Matrix (Fin 2) (Fin 2) F) 1 0 *
        (g : Matrix (Fin 2) (Fin 2) F) 1 1 + ((g : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹ =
        ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 + 1) /
          (g : Matrix (Fin 2) (Fin 2) F) 1 0 := by
      field_simp
    rw [this, hbc, mul_div_cancel_right₀ _ hc]
  ext i j
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_upperU, coe_swapW, coe_upperB,
    mul_fin_two, mul_fin_two]
  fin_cases i <;> fin_cases j
  · simp [div_mul_cancel₀ _ hc]
  · simpa using h01.symm
  · simp
  · simp

theorem eq_one_of_eq_inv {l : F} (hl0 : l ≠ 0) (h : l = l⁻¹) : l = 1 := by
  have h2 : l * l = 1 := by
    calc l * l = l * l⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ hl0
  have h3 : (l + 1) * (l + 1) = 0 := by
    calc (l + 1) * (l + 1) = l * l + (l + l) + 1 := by ring
      _ = 0 := by rw [h2, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have h4 : l + 1 = 0 := mul_self_eq_zero.mp h3
  calc l = l + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h4, zero_add]

theorem diag_entries_eq_zero {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (y : SpecialLinearGroup (Fin 2) F)
    (h : y * diagT l hl0 = diagT l⁻¹ (inv_ne_zero hl0) * y) :
    (y : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (y : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  have h0 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 1) h
  simp only [SpecialLinearGroup.coe_mul, coe_diagT] at h0 h1
  rw [eta_fin_two (y : Matrix (Fin 2) (Fin 2) F), mul_fin_two, mul_fin_two] at h0 h1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    mul_zero, zero_mul, add_zero, zero_add, Fin.isValue, inv_inv] at h0 h1
  have hne : l - l⁻¹ ≠ 0 := fun h' => hl1 (eq_one_of_eq_inv hl0 (sub_eq_zero.mp h'))
  constructor
  · have : (y : Matrix (Fin 2) (Fin 2) F) 0 0 * (l - l⁻¹) = 0 := by
      rw [mul_sub, h0, mul_comm]; ring
    exact (mul_eq_zero.mp this).resolve_right hne
  · have : (y : Matrix (Fin 2) (Fin 2) F) 1 1 * (l - l⁻¹) = 0 := by
      rw [mul_sub, h1, mul_comm]; ring
    exact (mul_eq_zero.mp this).resolve_right hne

theorem eq_one_of_sq_eq_one {c : F} (h : c * c = 1) : c = 1 := by
  have h3 : (c + 1) * (c + 1) = 0 := by
    calc (c + 1) * (c + 1) = c * c + (c + c) + 1 := by ring
      _ = 0 := by rw [h, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have h4 : c + 1 = 0 := mul_self_eq_zero.mp h3
  calc c = c + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h4, zero_add]

theorem eq_swapW_of {y : SpecialLinearGroup (Fin 2) F}
    (h00 : (y : Matrix (Fin 2) (Fin 2) F) 0 0 = 0) (h11 : (y : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)
    (h : upperU 1 * (y * upperU 1 * y⁻¹) * upperU 1 = y) : y = swapW := by
  have hd := det_eq y
  rw [h00, h11, zero_mul, zero_add] at hd
  have hY : (y : Matrix (Fin 2) (Fin 2) F) =
      !![0, (y : Matrix (Fin 2) (Fin 2) F) 0 1; (y : Matrix (Fin 2) (Fin 2) F) 1 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11]
  have h' := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv, coe_upperU] at h'
  rw [adjugate_fin_two, h00, h11, hY] at h'
  simp only [mul_fin_two, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, Fin.isValue, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
    CharTwo.neg_eq] at h'
  rw [hd] at h'
  have hcc : (y : Matrix (Fin 2) (Fin 2) F) 1 0 * (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    calc _ = 1 + (1 + (y : Matrix (Fin 2) (Fin 2) F) 1 0 * (y : Matrix (Fin 2) (Fin 2) F) 1 0) := by
          rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      _ = 1 := by rw [h', add_zero]
  have hc1 := eq_one_of_sq_eq_one hcc
  rw [hc1, mul_one] at hd
  ext i j
  rw [hY, coe_swapW]
  fin_cases i <;> fin_cases j <;> simp [hd, hc1]

theorem swapW_mul_self : (swapW : SpecialLinearGroup (Fin 2) F) * swapW = 1 := by
  ext i j
  rw [SpecialLinearGroup.coe_mul, coe_swapW, mul_fin_two, SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem swapW_inv : (swapW : SpecialLinearGroup (Fin 2) F)⁻¹ = swapW :=
  inv_eq_of_mul_eq_one_right swapW_mul_self

theorem swapW_conj_diagT (l : F) (hl : l ≠ 0) :
    swapW * diagT l hl * swapW⁻¹ = diagT l⁻¹ (inv_ne_zero hl) := by
  rw [swapW_inv]
  ext i j
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_swapW, coe_diagT, coe_diagT,
    mul_fin_two, mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

theorem upperU_mul_conj_mul : upperU (1 : F) * (swapW * upperU 1 * swapW⁻¹) * upperU 1 = swapW := by
  rw [swapW_inv]
  ext i j
  simp only [SpecialLinearGroup.coe_mul, coe_swapW, coe_upperU, mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem upperU_one_ten (x : F) : ((upperU x : SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp [coe_upperU]

omit [CharP F 2] in
theorem diagT_one_ten (l : F) (hl : l ≠ 0) : ((diagT l hl : SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp [coe_diagT]

omit [CharP F 2] in
theorem upperB_one_ten (c d : F) (hc : c ≠ 0) : ((upperB c d hc : SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp [coe_upperB]

theorem hom_eq_of_eq_on_borel {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1) {X : Type*} [Group X]
    (α ψ : X →* SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hker : ∀ x, α x = 1 → ψ x = 1)
    (hB : ∀ x, (α x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 → ψ x = α x) (x : X) : ψ x = α x := by
  have hfac : ∀ x y, α x = α y → ψ x = ψ y := fun x y h => by
    have := hker (x * y⁻¹) (by rw [map_mul, map_inv, h, mul_inv_cancel])
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have hBe : ∀ x (g : SpecialLinearGroup (Fin 2) F), α x = g →
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 → ψ x = g := fun x g hx hg => by
    rw [hB x (by rw [hx]; exact hg), hx]
  obtain ⟨xw, hxw⟩ := hα swapW
  obtain ⟨xh, hxh⟩ := hα (diagT l hl0)
  obtain ⟨xu, hxu⟩ := hα (upperU 1)
  have hψh := hBe xh _ hxh (diagT_one_ten l hl0)
  have hψu := hBe xu _ hxu (upperU_one_ten 1)
  have h1 : α (xw * xh * xw⁻¹) = diagT l⁻¹ (inv_ne_zero hl0) := by
    rw [map_mul, map_mul, map_inv, hxw, hxh, swapW_conj_diagT]
  have h2 := hBe _ _ h1 (diagT_one_ten _ _)
  rw [map_mul, map_mul, map_inv, hψh] at h2
  have h3 : ψ xw * diagT l hl0 = diagT l⁻¹ (inv_ne_zero hl0) * ψ xw := by
    rw [← h2]; group
  obtain ⟨h00, h11⟩ := diag_entries_eq_zero hl0 hl1 _ h3
  have h4 : α (xu * (xw * xu * xw⁻¹) * xu) = α xw := by
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, hxu, hxw, upperU_mul_conj_mul]
  have h5 := hfac _ _ h4
  rw [map_mul, map_mul, map_mul, map_mul, map_inv, hψu] at h5
  have hw : ψ xw = swapW := eq_swapW_of h00 h11 h5
  by_cases hc : (α x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · exact hB x hc
  · obtain ⟨x₁, hx₁⟩ := hα (upperU ((α x : Matrix (Fin 2) (Fin 2) F) 0 0 /
      (α x : Matrix (Fin 2) (Fin 2) F) 1 0))
    obtain ⟨x₂, hx₂⟩ := hα (upperB ((α x : Matrix (Fin 2) (Fin 2) F) 1 0)
      ((α x : Matrix (Fin 2) (Fin 2) F) 1 1) hc)
    have hdec := eq_upper_mul_swap_mul (α x) hc
    have h6 : α x = α (x₁ * xw * x₂) := by
      rw [map_mul, map_mul, hx₁, hxw, hx₂]
      exact hdec
    rw [hfac _ _ h6, map_mul, map_mul, hBe x₁ _ hx₁ (upperU_one_ten _), hw,
      hBe x₂ _ hx₂ (upperB_one_ten _ _ _)]
    exact hdec.symm

theorem cocycle_eq_zero {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1) {X : Type*} [Group X]
    (α : X →* SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α) (c : X → Fin 2 → F)
    (hc : ∀ x y, c (x * y) = c x + (α x : Matrix (Fin 2) (Fin 2) F).mulVec (c y))
    (hB : ∀ x, (α x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 → c x = 0) (x : X) : c x = 0 := by
  have hBe : ∀ x (g : SpecialLinearGroup (Fin 2) F), α x = g →
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 → c x = 0 := fun x g hx hg =>
    hB x (by rw [hx]; exact hg)
  obtain ⟨xw, hxw⟩ := hα swapW
  obtain ⟨xh, hxh⟩ := hα (diagT l hl0)
  have hch := hBe xh _ hxh (diagT_one_ten l hl0)
  have h1 : α (xw * xh * xw⁻¹) = diagT l⁻¹ (inv_ne_zero hl0) := by
    rw [map_mul, map_mul, map_inv, hxw, hxh, swapW_conj_diagT]
  have hct := hBe _ _ h1 (diagT_one_ten _ _)
  have h2 : c xw = (diagT l⁻¹ (inv_ne_zero hl0) : Matrix (Fin 2) (Fin 2) F).mulVec (c xw) := by
    have e1 := hc xw xh
    rw [hch, mulVec_zero, add_zero] at e1
    have e2 := hc (xw * xh * xw⁻¹) xw
    rw [hct, zero_add, h1, show xw * xh * xw⁻¹ * xw = xw * xh by group, e1] at e2
    exact e2
  have hw : c xw = 0 := by
    have h0 := congrFun h2 0
    have h1' := congrFun h2 1
    rw [coe_diagT] at h0 h1'
    simp only [mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, Fin.isValue, zero_mul, add_zero, zero_add,
      inv_inv] at h0 h1'
    have hne1 : l⁻¹ - 1 ≠ 0 := fun h => hl1 (by
      have := sub_eq_zero.mp h
      rwa [inv_eq_one] at this)
    have hne2 : l - 1 ≠ 0 := fun h => hl1 (sub_eq_zero.mp h)
    ext i
    fin_cases i
    · have : c xw 0 * (l⁻¹ - 1) = 0 := by rw [mul_sub, mul_one, mul_comm, ← h0, sub_self]
      simpa using (mul_eq_zero.mp this).resolve_right hne1
    · have : c xw 1 * (l - 1) = 0 := by rw [mul_sub, mul_one, mul_comm, ← h1', sub_self]
      simpa using (mul_eq_zero.mp this).resolve_right hne2
  by_cases hcx : (α x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · exact hB x hcx
  · obtain ⟨x₁, hx₁⟩ := hα (upperU ((α x : Matrix (Fin 2) (Fin 2) F) 0 0 /
      (α x : Matrix (Fin 2) (Fin 2) F) 1 0))
    obtain ⟨x₂, hx₂⟩ := hα (upperB ((α x : Matrix (Fin 2) (Fin 2) F) 1 0)
      ((α x : Matrix (Fin 2) (Fin 2) F) 1 1) hcx)
    have hdec := eq_upper_mul_swap_mul (α x) hcx
    have hk : α ((x₁ * xw * x₂)⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hx₁, hxw, hx₂, ← hdec, inv_mul_cancel]
    have hck := hBe _ _ hk (by simp)
    have hx : x = x₁ * xw * x₂ * ((x₁ * xw * x₂)⁻¹ * x) := by group
    rw [hx, hc, hck, mulVec_zero, add_zero, hc, hc, hw, hBe x₁ _ hx₁ (upperU_one_ten _),
      hBe x₂ _ hx₂ (upperB_one_ten _ _ _), mulVec_zero, mulVec_zero, add_zero, zero_add]

omit [CharP F 2] in
theorem upperU_add (x y : F) : upperU (x + y) = upperU x * upperU y := by
  ext i j
  rw [SpecialLinearGroup.coe_mul, coe_upperU, coe_upperU, coe_upperU, mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [add_comm]

omit [CharP F 2] in
theorem upperU_zero : upperU (0 : F) = 1 := by
  ext i j
  rw [coe_upperU, SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

@[expose] def upperHom : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun x := upperU (Multiplicative.toAdd x)
  map_one' := upperU_zero
  map_mul' _ _ := upperU_add _ _

@[expose] def unitri2 : Subgroup (SpecialLinearGroup (Fin 2) F) := (upperHom (F := F)).range

omit [CharP F 2] in
theorem mem_unitri2 {g : SpecialLinearGroup (Fin 2) F} : g ∈ unitri2 ↔ ∃ x : F, upperU x = g :=
  ⟨fun ⟨x, hx⟩ => ⟨Multiplicative.toAdd x, hx⟩, fun ⟨x, hx⟩ => ⟨Multiplicative.ofAdd x, hx⟩⟩

omit [CharP F 2] in
theorem upperHom_injective : Function.Injective (upperHom (F := F)) := by
  intro x y h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [upperHom, coe_upperU] using this

theorem conj_mem_unitri2 {g : SpecialLinearGroup (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) {u : SpecialLinearGroup (Fin 2) F}
    (hu : u ∈ unitri2) : g * u * g⁻¹ ∈ unitri2 := by
  obtain ⟨x, rfl⟩ := mem_unitri2.mp hu
  have hd := det_eq g
  rw [hg, mul_zero, add_zero] at hd
  refine mem_unitri2.mpr
    ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 * x, ?_⟩
  ext i j
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
    adjugate_fin_two, coe_upperU, coe_upperU, eta_fin_two (g : Matrix (Fin 2) (Fin 2) F), hg]
  simp only [mul_fin_two]
  fin_cases i <;> fin_cases j
  · simp [hd]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add, mul_one,
      CharTwo.neg_eq]
    rw [show (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 1 +
        ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * x + (g : Matrix (Fin 2) (Fin 2) F) 0 1) *
          (g : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 * x +
          ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 1 +
            (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 1) by ring,
      CharTwo.add_self_eq_zero, add_zero]
  · simp
  · simp [mul_comm, hd]

variable [Fintype F]

omit [CharP F 2] in
theorem card_unitri2 : Nat.card (unitri2 (F := F)) = Fintype.card F := by
  rw [unitri2, ← Nat.card_congr (MonoidHom.ofInjective upperHom_injective).toEquiv,
    ← Nat.card_eq_fintype_card]
  exact Nat.card_congr Multiplicative.toAdd

omit [Fintype F] in
theorem isPGroup_unitri2 : IsPGroup 2 (unitri2 (F := F)) := by
  intro u
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨x, hx⟩ := mem_unitri2.mp u.2
  rw [pow_one, Subgroup.coe_pow, ← hx, sq, ← upperU_add, CharTwo.add_self_eq_zero, upperU_zero,
    Subgroup.coe_one]

omit [CharP F 2] in
theorem card_SL2_eq : Nat.card (SpecialLinearGroup (Fin 2) F) =
    Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  rw [Matrix.card_SL_field]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Fintype.card F with hq
  have hq1 : 2 ≤ q := Fintype.one_lt_card
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub, mul_one, sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring]
  exact Nat.mul_div_cancel _ (by omega)

omit [CharP F 2] in
theorem not_two_dvd_index_unitri2 {k : ℕ} (hk : 1 ≤ k) (hF : Fintype.card F = 2 ^ k) :
    ¬ 2 ∣ (unitri2 (F := F)).index := by
  have h1 := (unitri2 (F := F)).card_mul_index
  rw [card_unitri2, card_SL2_eq, hF] at h1
  have h2 : (unitri2 (F := F)).index = (2 ^ k) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) h1
  rw [h2]
  have : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have he : Even ((2 ^ k) ^ 2) := by
    rw [← pow_mul]
    exact (Nat.even_pow' (by omega)).mpr even_two
  have ho : Odd ((2 ^ k) ^ 2 - 1) := Nat.Even.sub_odd this he odd_one
  exact Nat.not_even_iff_odd.mpr ho ∘ (even_iff_two_dvd.mpr)

theorem exists_conj_unitri2 {k : ℕ} (hk : 1 ≤ k) (hF : Fintype.card F = 2 ^ k)
    {P : Subgroup (SpecialLinearGroup (Fin 2) F)} (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) :
    ∃ g : SpecialLinearGroup (Fin 2) F, ∀ h, h ∈ P ↔ g⁻¹ * h * g ∈ unitri2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) F)
    (isPGroup_unitri2.toSylow (not_two_dvd_index_unitri2 hk hF)) (hP.toSylow hPi)
  refine ⟨g, fun h => ?_⟩
  have hg' := congrArg (fun S : Sylow 2 (SpecialLinearGroup (Fin 2) F) =>
    (S : Subgroup (SpecialLinearGroup (Fin 2) F))) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at hg'
  rw [← hg', Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]

end CFSG.Quasithin.H13.SL2Two
