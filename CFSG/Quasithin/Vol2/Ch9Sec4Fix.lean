module

public import CFSG.Quasithin.Vol2.Ch9Sec4Core

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Quasithin.H Matrix

namespace Om4Pt

variable {K : Type} [Field K]

@[expose] def fixM (φ : MulAut (Om4.VM K)) : Subgroup (Om4.VM K) where
  carrier := {X | φ X = X}
  mul_mem' {a b} ha hb := by
    show φ (a * b) = a * b
    rw [map_mul, show φ a = a from ha, show φ b = b from hb]
  one_mem' := map_one φ
  inv_mem' {a} ha := by
    show φ a⁻¹ = a⁻¹
    rw [map_inv, show φ a = a from ha]

theorem mem_fixM {φ : MulAut (Om4.VM K)} {X : Om4.VM K} : X ∈ fixM φ ↔ φ X = X := Iff.rfl

theorem card_fixM_mul_le [Finite K] {φ : MulAut (Om4.VM K)} {τ : K → K} {ω : K} (hω : τ ω ≠ ω)
    (hφ : ∀ (c : K) (X : Om4.VM K), Multiplicative.toAdd (φ (Multiplicative.ofAdd
      (c • Multiplicative.toAdd X))) = τ c • Multiplicative.toAdd (φ X)) :
    Nat.card (fixM φ) * Nat.card (fixM φ) ≤ Nat.card (Om4.VM K) := by
  let f : ↥(fixM φ) × ↥(fixM φ) → Om4.VM K := fun p =>
    (p.1 : Om4.VM K) * Multiplicative.ofAdd (ω • Multiplicative.toAdd (p.2 : Om4.VM K))
  have hf : Function.Injective f := by
    rintro ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ ⟨⟨X', hX'⟩, ⟨Y', hY'⟩⟩ h
    have h1 : Multiplicative.toAdd X + ω • Multiplicative.toAdd Y =
        Multiplicative.toAdd X' + ω • Multiplicative.toAdd Y' := by
      have := congrArg Multiplicative.toAdd h
      simpa [f] using this
    have hD : Y' * Y⁻¹ ∈ fixM φ := (fixM φ).mul_mem hY' ((fixM φ).inv_mem hY)
    have hE : X * X'⁻¹ ∈ fixM φ := (fixM φ).mul_mem hX ((fixM φ).inv_mem hX')
    have hED : X * X'⁻¹ = Multiplicative.ofAdd (ω • Multiplicative.toAdd (Y' * Y⁻¹)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_mul, toAdd_inv, smul_add, smul_neg]
      calc Multiplicative.toAdd X + -Multiplicative.toAdd X'
          = (Multiplicative.toAdd X + ω • Multiplicative.toAdd Y) -
            (Multiplicative.toAdd X' + ω • Multiplicative.toAdd Y) := by abel
        _ = (Multiplicative.toAdd X' + ω • Multiplicative.toAdd Y') -
            (Multiplicative.toAdd X' + ω • Multiplicative.toAdd Y) := by rw [h1]
        _ = ω • Multiplicative.toAdd Y' + -(ω • Multiplicative.toAdd Y) := by abel
    have h2 : φ (Multiplicative.ofAdd (ω • Multiplicative.toAdd (Y' * Y⁻¹))) =
        Multiplicative.ofAdd (ω • Multiplicative.toAdd (Y' * Y⁻¹)) := by
      rw [← hED]
      exact hE
    have h3 := congrArg Multiplicative.toAdd h2
    rw [hφ, show φ (Y' * Y⁻¹) = Y' * Y⁻¹ from hD, toAdd_ofAdd, ← sub_eq_zero, ← sub_smul] at h3
    have h4 : Multiplicative.toAdd (Y' * Y⁻¹) = 0 :=
      (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hω)
    have hYY : Y' = Y := by
      have h5 : Y' * Y⁻¹ = 1 := Multiplicative.toAdd.injective (by rw [h4, toAdd_one])
      exact mul_inv_eq_one.mp h5
    subst hYY
    have hXX : X = X' := Multiplicative.toAdd.injective (add_right_cancel h1)
    subst hXX
    rfl
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at h

theorem exists_eq_smul_add_smul_of_commute {A Y : Matrix (Fin 2) (Fin 2) K}
    (hA : ∀ a : K, A ≠ a • 1) (h : A * Y = Y * A) : ∃ x y : K, Y = x • 1 + y • A := by
  have h00 := congrFun₂ h 0 0
  have h01 := congrFun₂ h 0 1
  have h10 := congrFun₂ h 1 0
  have h11 := congrFun₂ h 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · have hd : A 0 0 - A 1 1 ≠ 0 := by
        intro hd
        apply hA (A 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc]
        linear_combination -hd
      have hq : Y 0 1 = 0 := by
        have : Y 0 1 * (A 0 0 - A 1 1) = 0 := by rw [hb] at h01; linear_combination h01
        exact (mul_eq_zero.mp this).resolve_right hd
      have hr : Y 1 0 = 0 := by
        have : Y 1 0 * (A 0 0 - A 1 1) = 0 := by rw [hc] at h10; linear_combination -h10
        exact (mul_eq_zero.mp this).resolve_right hd
      refine ⟨Y 0 0 - (Y 0 0 - Y 1 1) / (A 0 0 - A 1 1) * A 0 0,
        (Y 0 0 - Y 1 1) / (A 0 0 - A 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, hq, hr]
      · field_simp
        ring
    · refine ⟨Y 0 0 - Y 1 0 / A 1 0 * A 0 0, Y 1 0 / A 1 0, ?_⟩
      have hq : Y 0 1 = 0 := by
        have : Y 0 1 * A 1 0 = 0 := by rw [hb] at h00; linear_combination -h00
        exact (mul_eq_zero.mp this).resolve_right hc
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hq] <;> field_simp
      · linear_combination -h10
  · refine ⟨Y 0 0 - Y 0 1 / A 0 1 * A 0 0, Y 0 1 / A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
    · linear_combination h00
    · linear_combination h01

theorem card_le_of_det_eq_zero [CharP K 2] [Finite K] {F : Subgroup (Om4.VM K)}
    (hF : ∀ X ∈ F, (Multiplicative.toAdd X).det = 0) : Nat.card F ≤ Nat.card K * Nat.card K := by
  classical
  by_cases hbot : F = ⊥
  · rw [hbot, Subgroup.card_bot]
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
  obtain ⟨⟨X, hXF⟩, hX1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hX0 : Multiplicative.toAdd X ≠ 0 := fun h => hX1 (Subtype.ext
    (Multiplicative.toAdd.injective (by rw [h]; rfl)))
  obtain ⟨γ, hγ⟩ := exists_rho_eq_single hX0 (hF X hXF)
  set F' := F.map (Om4.rho γ).toMonoidHom with hF'
  have hcard : Nat.card F' = Nat.card F :=
    Subgroup.card_map_of_injective (Om4.rho γ).injective
  have hF'd : ∀ Y ∈ F', (Multiplicative.toAdd Y).det = 0 := by
    rintro _ ⟨Y, hY, rfl⟩
    show (Multiplicative.toAdd (Om4.rho γ Y)).det = 0
    rw [toAdd_rho, det_rho]
    exact hF Y hY
  have hE : Multiplicative.ofAdd !![(1 : K), 0; 0, 0] ∈ F' :=
    ⟨X, hXF, Multiplicative.toAdd.injective (by
      show Multiplicative.toAdd (Om4.rho γ X) = _
      rw [toAdd_rho, hγ, toAdd_ofAdd])⟩
  have h11 : ∀ Y ∈ F', Multiplicative.toAdd Y 1 1 = 0 := by
    intro Y hY
    have h1 := hF'd _ (F'.mul_mem hE hY)
    have h2 := hF'd Y hY
    rw [toAdd_mul, toAdd_ofAdd] at h1
    have h3 := detPolarCh6_eq !![(1 : K), 0; 0, 0] (Multiplicative.toAdd Y)
    rw [h1, h2] at h3
    simpa [detPolarCh6, Matrix.det_fin_two_of] using h3
  have h0110 : ∀ Y ∈ F', Multiplicative.toAdd Y 0 1 * Multiplicative.toAdd Y 1 0 = 0 := by
    intro Y hY
    have h2 := hF'd Y hY
    rw [Matrix.det_fin_two, h11 Y hY] at h2
    have h2' : -(Multiplicative.toAdd Y 0 1 * Multiplicative.toAdd Y 1 0) = 0 := by
      rw [← h2]; ring
    exact neg_eq_zero.mp h2'
  have hrc : (∀ Y ∈ F', Multiplicative.toAdd Y 1 0 = 0) ∨
      (∀ Y ∈ F', Multiplicative.toAdd Y 0 1 = 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨Y, hY, hY1⟩, ⟨Y', hY', hY'1⟩⟩ := hcon
    have hY01 : Multiplicative.toAdd Y 0 1 = 0 :=
      (mul_eq_zero.mp (h0110 Y hY)).resolve_right hY1
    have hY'10 : Multiplicative.toAdd Y' 1 0 = 0 :=
      (mul_eq_zero.mp (h0110 Y' hY')).resolve_left hY'1
    have h := h0110 _ (F'.mul_mem hY hY')
    rw [toAdd_mul, Matrix.add_apply, Matrix.add_apply, hY01, hY'10, zero_add, add_zero] at h
    exact mul_ne_zero hY'1 hY1 h
  rw [← hcard]
  rcases hrc with hr | hc
  · let g : ↥F' → K × K := fun Y => (Multiplicative.toAdd (Y : Om4.VM K) 0 0,
      Multiplicative.toAdd (Y : Om4.VM K) 0 1)
    have hg : Function.Injective g := by
      rintro ⟨Y, hY⟩ ⟨Y', hY'⟩ h
      simp only [g, Prod.mk.injEq] at h
      refine Subtype.ext (Multiplicative.toAdd.injective ?_)
      ext i j
      fin_cases i <;> fin_cases j
      · exact h.1
      · exact h.2
      · simp [hr Y hY, hr Y' hY']
      · simp [h11 Y hY, h11 Y' hY']
    have h := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_prod] at h
  · let g : ↥F' → K × K := fun Y => (Multiplicative.toAdd (Y : Om4.VM K) 0 0,
      Multiplicative.toAdd (Y : Om4.VM K) 1 0)
    have hg : Function.Injective g := by
      rintro ⟨Y, hY⟩ ⟨Y', hY'⟩ h
      simp only [g, Prod.mk.injEq] at h
      refine Subtype.ext (Multiplicative.toAdd.injective ?_)
      ext i j
      fin_cases i <;> fin_cases j
      · exact h.1
      · simp [hc Y hY, hc Y' hY']
      · exact h.2
      · simp [h11 Y hY, h11 Y' hY']
    have h := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_prod] at h

theorem card_le_of_commute [Finite K] {ι : Type*} [Finite ι] {A : Matrix (Fin 2) (Fin 2) K}
    (hA : ∀ a : K, A ≠ a • 1) {f : ι → Matrix (Fin 2) (Fin 2) K} (hf : Function.Injective f)
    (hc : ∀ i, A * f i = f i * A) : Nat.card ι ≤ Nat.card K * Nat.card K := by
  classical
  choose x y hxy using fun i => exists_eq_smul_add_smul_of_commute hA (hc i)
  have hg : Function.Injective fun i => (x i, y i) := by
    intro i j h
    simp only [Prod.mk.injEq] at h
    apply hf
    rw [hxy i, hxy j, h.1, h.2]
  have := Nat.card_le_card_of_injective _ hg
  rwa [Nat.card_prod] at this

theorem lr_eq_one_of_card_fixM [CharP K 2] [Fintype K] (hK4 : Fintype.card K = 4)
    (A B : GL (Fin 2) K) (hF : 32 ≤ Nat.card (fixM (Om4.lr A B))) : Om4.lr A B = 1 := by
  classical
  have hK : Nat.card K = 4 := by rw [Nat.card_eq_fintype_card, hK4]
  obtain ⟨X₀, hX₀F, hX₀⟩ : ∃ X₀ ∈ fixM (Om4.lr A B), (Multiplicative.toAdd X₀).det ≠ 0 := by
    by_contra hall
    push Not at hall
    have := card_le_of_det_eq_zero hall
    rw [hK] at this
    omega
  set Y₀ := Multiplicative.toAdd X₀ with hY₀
  have hu : IsUnit Y₀.det := isUnit_iff_ne_zero.mpr hX₀
  have hAu : (A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAu' : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hfix : ∀ Y ∈ fixM (Om4.lr A B), (A : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd Y *
      (B : Matrix (Fin 2) (Fin 2) K)ᵀ = Multiplicative.toAdd Y := fun Y hY => by
    have := congrArg Multiplicative.toAdd (mem_fixM.mp hY)
    rwa [Om4.toAdd_lr] at this
  have h0 := hfix X₀ hX₀F
  rw [← hY₀] at h0
  have hB : (B : Matrix (Fin 2) (Fin 2) K)ᵀ =
      Y₀⁻¹ * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y₀ := by
    calc (B : Matrix (Fin 2) (Fin 2) K)ᵀ
        = Y₀⁻¹ * (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          ((A : Matrix (Fin 2) (Fin 2) K) * Y₀ * (B : Matrix (Fin 2) (Fin 2) K)ᵀ)) := by
          rw [show Y₀⁻¹ * (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
              ((A : Matrix (Fin 2) (Fin 2) K) * Y₀ * (B : Matrix (Fin 2) (Fin 2) K)ᵀ)) =
              Y₀⁻¹ * ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
                (A : Matrix (Fin 2) (Fin 2) K)) * Y₀ * (B : Matrix (Fin 2) (Fin 2) K)ᵀ) by
              simp only [Matrix.mul_assoc], hAu', Matrix.one_mul, ← Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = _ := by rw [h0, Matrix.mul_assoc]
  by_cases hs : ∃ a : K, (A : Matrix (Fin 2) (Fin 2) K) = a • 1
  · obtain ⟨a, ha⟩ := hs
    have hAi : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = a⁻¹ • 1 := by
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ha
        have := hAu
        rw [ha, Matrix.zero_mul] at this
        exact zero_ne_one this
      calc ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          = (a⁻¹ • 1 : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K) *
            ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
            rw [← Matrix.mul_assoc, ha, Matrix.smul_mul, Matrix.one_mul, smul_smul,
              inv_mul_cancel₀ ha0, one_smul, Matrix.one_mul]
        _ = a⁻¹ • 1 := by rw [hAu, Matrix.mul_one]
    refine MulEquiv.ext fun Y => Multiplicative.toAdd.injective ?_
    rw [Om4.toAdd_lr, MulAut.one_apply, hB, ha, hAi]
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      have := hAu
      rw [ha, Matrix.zero_mul] at this
      exact zero_ne_one this
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ ha0, one_smul, Matrix.nonsing_inv_mul _ hu]
  · push Not at hs
    exfalso
    have hcomm : ∀ Y : ↥(fixM (Om4.lr A B)), (A : Matrix (Fin 2) (Fin 2) K) *
        (Multiplicative.toAdd (Y : Om4.VM K) * Y₀⁻¹) =
        (Multiplicative.toAdd (Y : Om4.VM K) * Y₀⁻¹) * (A : Matrix (Fin 2) (Fin 2) K) := by
      rintro ⟨Y, hY⟩
      have h1 := hfix Y hY
      rw [hB] at h1
      calc (A : Matrix (Fin 2) (Fin 2) K) * (Multiplicative.toAdd Y * Y₀⁻¹)
          = ((A : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd Y *
            (Y₀⁻¹ * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y₀)) * Y₀⁻¹ *
            (A : Matrix (Fin 2) (Fin 2) K) := by
            simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hAu',
              Matrix.mul_one]
        _ = _ := by rw [h1]
    have hinj : Function.Injective fun Y : ↥(fixM (Om4.lr A B)) =>
        Multiplicative.toAdd (Y : Om4.VM K) * Y₀⁻¹ := by
      intro Y Y' h
      have h' := congrArg (· * Y₀) h
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one] at h'
      exact Subtype.ext (Multiplicative.toAdd.injective h')
    have := card_le_of_commute hs hinj hcomm
    rw [hK] at this
    omega

theorem detPolar_mul_mul [CharP K 2] (P R X Y : Matrix (Fin 2) (Fin 2) K) :
    detPolarCh6 (P * X * R) (P * Y * R) = P.det * R.det * detPolarCh6 X Y := by
  rw [detPolarCh6_eq, detPolarCh6_eq, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  ring

theorem transpose_sub_eq [CharP K 2] (M : Matrix (Fin 2) (Fin 2) K) :
    Mᵀ - M = (M 1 0 - M 0 1) • !![(0 : K), 1; 1, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  linear_combination (M 0 1 - M 1 0) * h2

theorem fix_lr_trM [CharP K 2] [Fintype K] (hK4 : Fintype.card K = 4) (A B : GL (Fin 2) K)
    (hF : 32 ≤ Nat.card (fixM (Om4.lr A B * Om4.trM))) :
    ∃ X₁ : Matrix (Fin 2) (Fin 2) K, X₁.det ≠ 0 ∧
      (∀ Y, Y ∈ fixM (Om4.lr A B * Om4.trM) ↔ Y ∈ perpM X₁) ∧
      ∀ Y : Om4.VM K, ∃ c : K, Multiplicative.toAdd ((Om4.lr A B * Om4.trM : MulAut (Om4.VM K)) Y) -
        Multiplicative.toAdd Y = c • X₁ := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hK : Nat.card K = 4 := by rw [Nat.card_eq_fintype_card, hK4]
  set φ : MulAut (Om4.VM K) := Om4.lr A B * Om4.trM with hφ
  have hφY : ∀ Y : Om4.VM K, Multiplicative.toAdd (φ Y) =
      (A : Matrix (Fin 2) (Fin 2) K) * (Multiplicative.toAdd Y)ᵀ *
        (B : Matrix (Fin 2) (Fin 2) K)ᵀ := fun Y => rfl
  obtain ⟨X₀, hX₀F, hX₀⟩ : ∃ X₀ ∈ fixM φ, (Multiplicative.toAdd X₀).det ≠ 0 := by
    by_contra hall
    push Not at hall
    have := card_le_of_det_eq_zero hall
    rw [hK] at this
    omega
  set Y₀ := Multiplicative.toAdd X₀ with hY₀
  have hu : IsUnit Y₀.det := isUnit_iff_ne_zero.mpr hX₀
  have huT : IsUnit Y₀ᵀ.det := by rwa [Matrix.det_transpose]
  set a : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with ha
  set a' : Matrix (Fin 2) (Fin 2) K := ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    with ha'
  have haa' : a * a' = 1 := by rw [ha, ha', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ha'a : a' * a = 1 := by rw [ha, ha', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h0 : a * Y₀ᵀ * (B : Matrix (Fin 2) (Fin 2) K)ᵀ = Y₀ := by
    rw [← hφY]
    exact congrArg Multiplicative.toAdd (mem_fixM.mp hX₀F)
  have hB : (B : Matrix (Fin 2) (Fin 2) K)ᵀ = (Y₀ᵀ)⁻¹ * a' * Y₀ := by
    have e : (Y₀ᵀ)⁻¹ * a' * Y₀ =
        (Y₀ᵀ)⁻¹ * (a' * (a * Y₀ᵀ * (B : Matrix (Fin 2) (Fin 2) K)ᵀ)) := by
      rw [h0, Matrix.mul_assoc]
    rw [e, ← Matrix.mul_assoc a', ← Matrix.mul_assoc a', ha'a, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ huT, Matrix.one_mul]
  set C := Y₀⁻¹ * a with hC
  set C' := a' * Y₀ with hC'
  have hCC' : C * C' = 1 := by
    rw [hC, hC', Matrix.mul_assoc, ← Matrix.mul_assoc a, haa', Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hu]
  have hC'C : C' * C = 1 := by
    rw [hC, hC', Matrix.mul_assoc, ← Matrix.mul_assoc Y₀, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mul, ha'a]
  have hform : ∀ Y : Om4.VM K, Multiplicative.toAdd (φ Y) =
      Y₀ * C * (Y₀⁻¹ * Multiplicative.toAdd Y)ᵀ * C' := by
    intro Y
    rw [hφY, hB, Matrix.transpose_mul, hC, hC', ← Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have hfixiff : ∀ Y : Om4.VM K, Y ∈ fixM φ ↔
      C * (Y₀⁻¹ * Multiplicative.toAdd Y)ᵀ = (Y₀⁻¹ * Multiplicative.toAdd Y) * C := by
    intro Y
    rw [mem_fixM]
    constructor
    · intro hY
      have h1 := congrArg Multiplicative.toAdd hY
      rw [hform] at h1
      calc C * (Y₀⁻¹ * Multiplicative.toAdd Y)ᵀ
          = Y₀⁻¹ * (Y₀ * C * (Y₀⁻¹ * Multiplicative.toAdd Y)ᵀ * C') * C := by
            simp only [Matrix.mul_assoc, hC'C, Matrix.mul_one,
              Matrix.nonsing_inv_mul_cancel_left _ _ hu]
        _ = (Y₀⁻¹ * Multiplicative.toAdd Y) * C := by rw [h1]
    · intro hY
      apply Multiplicative.toAdd.injective
      rw [hform, Matrix.mul_assoc Y₀ C, hY]
      simp only [Matrix.mul_assoc, hCC', Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  set D := Cᵀ * C' with hD
  have hDcomm : ∀ Y : ↥(fixM φ), D * (Y₀⁻¹ * Multiplicative.toAdd (Y : Om4.VM K)) =
      (Y₀⁻¹ * Multiplicative.toAdd (Y : Om4.VM K)) * D := by
    rintro ⟨Y, hY⟩
    set Z := Y₀⁻¹ * Multiplicative.toAdd Y with hZ
    have h1 : C * Zᵀ = Z * C := (hfixiff Y).mp hY
    have h2 : Zᵀ = C' * Z * C := by
      calc Zᵀ = C' * (C * Zᵀ) := by rw [← Matrix.mul_assoc, hC'C, Matrix.one_mul]
        _ = C' * Z * C := by rw [h1, ← Matrix.mul_assoc]
    have h3 : Z * Cᵀ = Cᵀ * Zᵀ := by
      have := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_mul C Zᵀ, Matrix.transpose_transpose, Matrix.transpose_mul Z C]
        at this
    show Cᵀ * C' * Z = Z * (Cᵀ * C')
    calc Cᵀ * C' * Z = Cᵀ * (C' * Z * C) * C' := by
          simp only [Matrix.mul_assoc, hCC', Matrix.mul_one]
      _ = Z * (Cᵀ * C') := by rw [← h2, ← h3, Matrix.mul_assoc]
  have hDs : ∃ d : K, D = d • 1 := by
    by_contra hns
    push Not at hns
    have hinj : Function.Injective fun Y : ↥(fixM φ) =>
        Y₀⁻¹ * Multiplicative.toAdd (Y : Om4.VM K) := by
      intro Y Y' h
      have h' := congrArg (Y₀ * ·) h
      simp only [Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h'
      exact Subtype.ext (Multiplicative.toAdd.injective h')
    have := card_le_of_commute hns hinj hDcomm
    rw [hK] at this
    omega
  obtain ⟨d, hd⟩ := hDs
  have hCT : Cᵀ = d • C := by
    calc Cᵀ = D * C := by rw [hD, Matrix.mul_assoc, hC'C, Matrix.mul_one]
      _ = d • C := by rw [hd, Matrix.smul_mul, Matrix.one_mul]
  have hCsym : Cᵀ = C := by
    have h1 : C = (d * d) • C := by
      calc C = (Cᵀ)ᵀ := (Matrix.transpose_transpose C).symm
        _ = (d * d) • C := by rw [hCT, Matrix.transpose_smul, hCT, smul_smul]
    have hC0 : C ≠ 0 := by
      intro h0
      rw [h0, Matrix.zero_mul] at hCC'
      exact zero_ne_one hCC'
    have hdd : d * d = 1 := by
      by_contra hne
      have h3 : (d * d - 1) • C = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      exact hC0 ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne))
    have hd1 : d = 1 := by
      have h4 : (d - 1) * (d - 1) = 0 := by linear_combination hdd - (d - 1) * h2
      have := mul_self_eq_zero.mp h4
      exact sub_eq_zero.mp this
    rw [hCT, hd1, one_smul]
  set J : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0] with hJ
  have hJd : J.det ≠ 0 := by
    rw [hJ, Matrix.det_fin_two_of]
    simp
  have hC'd : C'.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hCC'
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨Y₀ * J * C', by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hX₀ hJd) hC'd, fun Y => ?_, fun Y => ?_⟩
  ·
    set Z := Y₀⁻¹ * Multiplicative.toAdd Y with hZ
    have hYZ : Y₀ * (Z * C) * C' = Multiplicative.toAdd Y := by
      simp only [Matrix.mul_assoc, hCC', Matrix.mul_one, hZ,
        Matrix.mul_nonsing_inv_cancel_left _ _ hu]
    have hsym : C * Zᵀ = Z * C ↔ (Z * C) 1 0 + (Z * C) 0 1 = 0 := by
      have e1 : C * Zᵀ = (Z * C)ᵀ := by rw [Matrix.transpose_mul Z C, hCsym]
      rw [e1]
      constructor
      · intro h
        have := congrFun₂ h 1 0
        rw [Matrix.transpose_apply] at this
        rw [this]
        linear_combination (Z * C) 1 0 * h2
      · intro h
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
        · linear_combination h - (Z * C) 0 1 * h2
        · linear_combination h - (Z * C) 1 0 * h2
    rw [hfixiff]
    change C * Zᵀ = Z * C ↔ detPolarCh6 (Y₀ * J * C') (Multiplicative.toAdd Y) = 0
    rw [hsym, ← hYZ, detPolar_mul_mul]
    simp only [detPolarCh6, hJ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, one_mul,
      zero_add]
    constructor
    · intro h; rw [h, mul_zero]
    · intro h
      exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hX₀ hC'd)
  ·
    set Z := Y₀⁻¹ * Multiplicative.toAdd Y with hZ
    refine ⟨(Z * C) 1 0 - (Z * C) 0 1, ?_⟩
    have hYZ : Y₀ * (Z * C) * C' = Multiplicative.toAdd Y := by
      simp only [Matrix.mul_assoc, hCC', Matrix.mul_one, hZ,
        Matrix.mul_nonsing_inv_cancel_left _ _ hu]
    have e1 : C * Zᵀ = (Z * C)ᵀ := by rw [Matrix.transpose_mul Z C, hCsym]
    rw [hform]
    change Y₀ * C * Zᵀ * C' - Multiplicative.toAdd Y = _
    rw [Matrix.mul_assoc Y₀ C, e1, ← hYZ, ← Matrix.sub_mul, ← Matrix.mul_sub, transpose_sub_eq,
      Matrix.mul_smul, Matrix.smul_mul]

theorem frM_eq_one {τ : K ≃+* K} (hτ : ∀ c, τ c = c) : Om4.frM τ = 1 := by
  refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
  rw [Om4.toAdd_frM, MulAut.one_apply]
  ext i j
  simp [hτ]

theorem fix_classify [CharP K 2] [Fintype K] (hK4 : Fintype.card K = 4) (A B : GL (Fin 2) K)
    (τ : K ≃+* K) {φ : MulAut (Om4.VM K)}
    (hφ : φ = Om4.lr A B * Om4.frM τ ∨ φ = Om4.lr A B * Om4.frM τ * Om4.trM)
    (hF : 32 ≤ Nat.card (fixM φ)) :
    φ = 1 ∨ ∃ X₁ : Matrix (Fin 2) (Fin 2) K, X₁.det ≠ 0 ∧ (∀ Y, Y ∈ fixM φ ↔ Y ∈ perpM X₁) ∧
      ∀ Y : Om4.VM K, ∃ c : K, Multiplicative.toAdd (φ Y) - Multiplicative.toAdd Y = c • X₁ := by
  have hV : Nat.card (Om4.VM K) = 256 := by
    rw [show Nat.card (Om4.VM K) = Nat.card (Fin 2 → Fin 2 → K) from rfl, Nat.card_fun,
      Nat.card_fun, Nat.card_eq_fintype_card (α := K), hK4]
    simp
  have hτ : ∀ c, τ c = c := by
    by_contra h
    push Not at h
    obtain ⟨ω, hω⟩ := h
    have hsemi : ∀ (c : K) (X : Om4.VM K), Multiplicative.toAdd (φ (Multiplicative.ofAdd
        (c • Multiplicative.toAdd X))) = τ c • Multiplicative.toAdd (φ X) := by
      intro c X
      rcases hφ with rfl | rfl
      · simpa using toAdd_lr_frM_smul A B τ c (Multiplicative.toAdd X)
      · simpa using toAdd_lr_frM_trM_smul A B τ c (Multiplicative.toAdd X)
    have := card_fixM_mul_le hω hsemi
    rw [hV] at this
    nlinarith
  rw [frM_eq_one hτ, mul_one] at hφ
  rcases hφ with rfl | rfl
  · exact Or.inl (lr_eq_one_of_card_fixM hK4 A B hF)
  · exact Or.inr (fix_lr_trM hK4 A B hF)

theorem card_perpM_mul_le [CharP K 2] [Finite K] {X₁ : Matrix (Fin 2) (Fin 2) K} (hX₁ : X₁ ≠ 0) :
    Nat.card (perpM X₁) * Nat.card K ≤ Nat.card (Om4.VM K) := by
  obtain ⟨E₀, hE₀⟩ : ∃ E₀, detPolarCh6 X₁ E₀ = 1 := by
    by_contra hall
    push Not at hall
    apply hX₁
    have h0 : ∀ Y, detPolarCh6 X₁ Y = 0 * detPolarCh6 X₁ Y := by
      intro Y
      by_contra hY
      rw [zero_mul] at hY
      apply hall ((detPolarCh6 X₁ Y)⁻¹ • Y)
      rw [detPolar_smul_right, inv_mul_cancel₀ hY]
    have := eq_smul_of_detPolar (X₀ := X₁) h0
    rwa [zero_smul] at this
  let f : ↥(perpM X₁) × K → Om4.VM K := fun p =>
    (p.1 : Om4.VM K) * Multiplicative.ofAdd (p.2 • E₀)
  have hf : Function.Injective f := by
    rintro ⟨⟨P, hP⟩, c⟩ ⟨⟨P', hP'⟩, c'⟩ h
    have h1 : Multiplicative.toAdd P + c • E₀ = Multiplicative.toAdd P' + c' • E₀ := by
      have := congrArg Multiplicative.toAdd h
      simpa [f] using this
    have h2 := congrArg (detPolarCh6 X₁) h1
    rw [detPolar_add_right, detPolar_add_right, detPolar_smul_right, detPolar_smul_right, hE₀,
      show detPolarCh6 X₁ (Multiplicative.toAdd P) = 0 from hP,
      show detPolarCh6 X₁ (Multiplicative.toAdd P') = 0 from hP', zero_add, zero_add, mul_one,
      mul_one] at h2
    subst h2
    have hPP : P = P' := Multiplicative.toAdd.injective (add_right_cancel h1)
    subst hPP
    rfl
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at h

theorem exists_smul_mem_of_le_perpM [CharP K 2] [Fintype K] (hK4 : Fintype.card K = 4)
    {X₁ Y₁ : Matrix (Fin 2) (Fin 2) K} (hX₁ : X₁ ≠ 0) (hY : detPolarCh6 X₁ Y₁ = 0)
    {U : Subgroup (Om4.VM K)} (hU : U ≤ perpM X₁) (hcard : 32 ≤ Nat.card U) :
    ∃ c : K, c ≠ 0 ∧ Multiplicative.ofAdd (c • Y₁) ∈ U := by
  have hK : Nat.card K = 4 := by rw [Nat.card_eq_fintype_card, hK4]
  have hV : Nat.card (Om4.VM K) = 256 := by
    rw [show Nat.card (Om4.VM K) = Nat.card (Fin 2 → Fin 2 → K) from rfl, Nat.card_fun,
      Nat.card_fun, hK]
    simp
  have hP := card_perpM_mul_le hX₁
  rw [hV, hK] at hP
  by_contra hall
  push Not at hall
  let f : K × ↥U → ↥(perpM X₁) := fun p => ⟨Multiplicative.ofAdd (p.1 • Y₁) * (p.2 : Om4.VM K),
    (perpM X₁).mul_mem (by
      show detPolarCh6 X₁ (Multiplicative.toAdd (Multiplicative.ofAdd (p.1 • Y₁))) = 0
      rw [toAdd_ofAdd, detPolar_smul_right, hY, mul_zero]) (hU p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨c, ⟨u, hu⟩⟩ ⟨c', ⟨u', hu'⟩⟩ h
    have h1 : c • Y₁ + Multiplicative.toAdd u = c' • Y₁ + Multiplicative.toAdd u' := by
      have := congrArg (fun x : ↥(perpM X₁) => Multiplicative.toAdd (x : Om4.VM K)) h
      simpa [f] using this
    have hcc : c = c' := by
      by_contra hne
      have h2 : Multiplicative.ofAdd ((c - c') • Y₁) ∈ U := by
        have h3 : Multiplicative.ofAdd ((c - c') • Y₁) = u' * u⁻¹ := by
          apply Multiplicative.toAdd.injective
          rw [toAdd_ofAdd, toAdd_mul, toAdd_inv, sub_smul]
          calc c • Y₁ - c' • Y₁
              = (c • Y₁ + Multiplicative.toAdd u) - (c' • Y₁ + Multiplicative.toAdd u) := by abel
            _ = (c' • Y₁ + Multiplicative.toAdd u') - (c' • Y₁ + Multiplicative.toAdd u) := by
                rw [h1]
            _ = Multiplicative.toAdd u' + -Multiplicative.toAdd u := by abel
        rw [h3]
        exact U.mul_mem hu' (U.inv_mem hu)
      exact hall (c - c') (sub_ne_zero.mpr hne) h2
    subst hcc
    have huu : u = u' := Multiplicative.toAdd.injective (add_left_cancel h1)
    subst huu
    rfl
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hK] at h
  omega

end Om4Pt

end CFSG.Quasithin.H13.Ch9
