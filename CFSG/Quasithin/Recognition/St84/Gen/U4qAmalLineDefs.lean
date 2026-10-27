module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

@[expose] def u4Herm : Submodule h.fixedField (Matrix (Fin 2) (Fin 2) K) where
  carrier := {X | ∀ i j, h.bar (X i j) = X j i}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    intro i j
    rw [Matrix.add_apply, map_add, hX i j, hY i j, Matrix.add_apply]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro i j
    rw [Matrix.zero_apply, map_zero, Matrix.zero_apply]
  smul_mem' c X hX := by
    simp only [Set.mem_setOf_eq] at hX ⊢
    intro i j
    have hc : h.bar (c : K) = c := (h.mem_fixedField).mp c.2
    change h.bar ((c : K) * X i j) = (c : K) * X j i
    rw [map_mul, hc, hX i j]

theorem mem_u4Herm {X : Matrix (Fin 2) (Fin 2) K} :
    X ∈ u4Herm h ↔ ∀ i j, h.bar (X i j) = X j i :=
  Iff.rfl

theorem mem_u4Herm_iff_map {X : Matrix (Fin 2) (Fin 2) K} :
    X ∈ u4Herm h ↔ X.map h.bar = Xᵀ := by
  rw [mem_u4Herm]
  constructor
  · intro hX
    ext i j
    exact hX i j
  · intro hX i j
    exact congrFun (congrFun hX i) j

theorem mem_u4Herm_iff_pow {X : Matrix (Fin 2) (Fin 2) K} :
    X ∈ u4Herm h ↔ X.map (· ^ 2 ^ m) = Xᵀ :=
  mem_u4Herm_iff_map h

theorem twist_mem_u4Herm (A : Matrix (Fin 2) (Fin 2) K) {X : Matrix (Fin 2) (Fin 2) K}
    (hX : X ∈ u4Herm h) : A * X * (A.map h.bar)ᵀ ∈ u4Herm h := by
  rw [mem_u4Herm] at hX ⊢
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
    map_add, map_mul, h.bar_bar, hX]
  ring

@[expose] noncomputable def u4Omega : K :=
  Classical.choose h.exists_bar_ne

theorem bar_u4Omega_ne : h.bar (u4Omega h) ≠ u4Omega h :=
  Classical.choose_spec h.exists_bar_ne

theorem u4Omega_add_bar_ne_zero : u4Omega h + h.bar (u4Omega h) ≠ 0 := by
  haveI := h.charP
  intro h0
  apply bar_u4Omega_ne h
  rw [eq_neg_of_add_eq_zero_right h0, CharTwo.neg_eq]

@[expose] noncomputable def u4Im (z : K) : K :=
  (z + h.bar z) / (u4Omega h + h.bar (u4Omega h))

@[expose] noncomputable def u4Re (z : K) : K :=
  z + u4Im h z * u4Omega h

theorem bar_u4Im (z : K) : h.bar (u4Im h z) = u4Im h z := by
  rw [u4Im, map_div₀, map_add, map_add, h.bar_bar, h.bar_bar, add_comm (h.bar z),
    add_comm (h.bar (u4Omega h))]

theorem u4Im_mul (z : K) : u4Im h z * (u4Omega h + h.bar (u4Omega h)) = z + h.bar z :=
  div_mul_cancel₀ _ (u4Omega_add_bar_ne_zero h)

theorem bar_u4Re (z : K) : h.bar (u4Re h z) = u4Re h z := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb := u4Im_mul h z
  rw [u4Re, map_add, map_mul, bar_u4Im]
  linear_combination hb + (h.bar z - u4Im h z * u4Omega h) * h2

theorem u4Re_add_u4Im_mul (z : K) : u4Re h z + u4Im h z * u4Omega h = z := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [u4Re]
  linear_combination (u4Im h z * u4Omega h) * h2

theorem u4Im_add_mul {a b : K} (ha : h.bar a = a) (hb : h.bar b = b) :
    u4Im h (a + b * u4Omega h) = b := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [u4Im, div_eq_iff (u4Omega_add_bar_ne_zero h), map_add, map_mul, ha, hb]
  linear_combination a * h2

theorem u4Re_add_mul {a b : K} (ha : h.bar a = a) (hb : h.bar b = b) :
    u4Re h (a + b * u4Omega h) = a := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [u4Re, u4Im_add_mul h ha hb]
  linear_combination (b * u4Omega h) * h2

theorem u4Im_add (z w : K) : u4Im h (z + w) = u4Im h z + u4Im h w := by
  rw [u4Im, u4Im, u4Im, map_add, ← add_div]
  congr 1
  ring

theorem u4Im_smul {c : K} (hc : h.bar c = c) (z : K) : u4Im h (c * z) = c * u4Im h z := by
  rw [u4Im, u4Im, map_mul, hc, ← mul_add, mul_div_assoc]

theorem u4Re_add (z w : K) : u4Re h (z + w) = u4Re h z + u4Re h w := by
  rw [u4Re, u4Re, u4Re, u4Im_add]
  ring

theorem u4Re_smul {c : K} (hc : h.bar c = c) (z : K) : u4Re h (c * z) = c * u4Re h z := by
  rw [u4Re, u4Re, u4Im_smul h hc]
  ring

@[expose] noncomputable def u4HermCoord : ↥(u4Herm h) ≃ₗ[h.fixedField] (Fin 4 → h.fixedField) where
  toFun X := ![⟨(X : Matrix (Fin 2) (Fin 2) K) 0 0,
      (h.mem_fixedField).mpr ((mem_u4Herm h).mp X.2 0 0)⟩,
    ⟨(X : Matrix (Fin 2) (Fin 2) K) 1 1, (h.mem_fixedField).mpr ((mem_u4Herm h).mp X.2 1 1)⟩,
    ⟨u4Re h ((X : Matrix (Fin 2) (Fin 2) K) 0 1), (h.mem_fixedField).mpr (bar_u4Re h _)⟩,
    ⟨u4Im h ((X : Matrix (Fin 2) (Fin 2) K) 0 1), (h.mem_fixedField).mpr (bar_u4Im h _)⟩]
  map_add' X Y := by
    funext k
    fin_cases k <;> apply Subtype.ext <;> simp [u4Re_add, u4Im_add]
  map_smul' c X := by
    have hc : h.bar (c : K) = c := (h.mem_fixedField).mp c.2
    funext k
    fin_cases k <;> apply Subtype.ext <;>
      simp [Subfield.smul_def, u4Re_smul h hc, u4Im_smul h hc]
  invFun v := ⟨!![(v 0 : K), (v 2 : K) + (v 3 : K) * u4Omega h;
      (v 2 : K) + (v 3 : K) * h.bar (u4Omega h), (v 1 : K)], by
    have h0 : h.bar (v 0 : K) = v 0 := (h.mem_fixedField).mp (v 0).2
    have h1 : h.bar (v 1 : K) = v 1 := (h.mem_fixedField).mp (v 1).2
    have h2 : h.bar (v 2 : K) = v 2 := (h.mem_fixedField).mp (v 2).2
    have h3 : h.bar (v 3 : K) = v 3 := (h.mem_fixedField).mp (v 3).2
    rw [mem_u4Herm]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h3, h.bar_bar]⟩
  left_inv X := by
    have hX := (mem_u4Herm h).mp X.2
    have e := congrArg h.bar (u4Re_add_u4Im_mul h ((X : Matrix (Fin 2) (Fin 2) K) 0 1))
    rw [map_add, map_mul, bar_u4Re, bar_u4Im, hX 0 1] at e
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simpa using u4Re_add_u4Im_mul h ((X : Matrix (Fin 2) (Fin 2) K) 0 1)
    · simpa using e
    · simp
  right_inv v := by
    have h2 : h.bar (v 2 : K) = v 2 := (h.mem_fixedField).mp (v 2).2
    have h3 : h.bar (v 3 : K) = v 3 := (h.mem_fixedField).mp (v 3).2
    funext k
    fin_cases k <;> apply Subtype.ext
    · simp
    · simp
    · simpa using u4Re_add_mul h h2 h3
    · simpa using u4Im_add_mul h h2 h3

theorem u4HermCoord_apply_zero (X : ↥(u4Herm h)) :
    (u4HermCoord h X 0 : K) = (X : Matrix (Fin 2) (Fin 2) K) 0 0 :=
  rfl

theorem u4HermCoord_apply_one (X : ↥(u4Herm h)) :
    (u4HermCoord h X 1 : K) = (X : Matrix (Fin 2) (Fin 2) K) 1 1 :=
  rfl

theorem u4HermCoord_apply_two (X : ↥(u4Herm h)) :
    (u4HermCoord h X 2 : K) = u4Re h ((X : Matrix (Fin 2) (Fin 2) K) 0 1) :=
  rfl

theorem u4HermCoord_apply_three (X : ↥(u4Herm h)) :
    (u4HermCoord h X 3 : K) = u4Im h ((X : Matrix (Fin 2) (Fin 2) K) 0 1) :=
  rfl

theorem coe_u4HermCoord_symm (v : Fin 4 → h.fixedField) :
    (((u4HermCoord h).symm v : ↥(u4Herm h)) : Matrix (Fin 2) (Fin 2) K) =
      !![(v 0 : K), (v 2 : K) + (v 3 : K) * u4Omega h;
        (v 2 : K) + (v 3 : K) * h.bar (u4Omega h), (v 1 : K)] :=
  rfl

@[expose] noncomputable def u4TwistLin (A : Matrix (Fin 2) (Fin 2) K) :
    ↥(u4Herm h) →ₗ[h.fixedField] ↥(u4Herm h) where
  toFun X := ⟨A * (X : Matrix (Fin 2) (Fin 2) K) * (A.map h.bar)ᵀ, twist_mem_u4Herm h A X.2⟩
  map_add' X Y := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    apply Subtype.ext
    simp [Matrix.mul_smul, Matrix.smul_mul]

theorem coe_u4TwistLin (A : Matrix (Fin 2) (Fin 2) K) (X : ↥(u4Herm h)) :
    ((u4TwistLin h A X : ↥(u4Herm h)) : Matrix (Fin 2) (Fin 2) K) =
      A * (X : Matrix (Fin 2) (Fin 2) K) * (A.map h.bar)ᵀ :=
  rfl

theorem u4TwistLin_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    u4TwistLin h (A * B) = (u4TwistLin h A).comp (u4TwistLin h B) := by
  refine LinearMap.ext fun X => Subtype.ext ?_
  simp only [LinearMap.comp_apply, coe_u4TwistLin, Matrix.map_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]

theorem u4TwistLin_one : u4TwistLin h 1 = LinearMap.id := by
  refine LinearMap.ext fun X => Subtype.ext ?_
  rw [coe_u4TwistLin, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one,
    Matrix.one_mul, Matrix.mul_one, LinearMap.id_apply]

@[expose] noncomputable def u4TwistMat (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 4) (Fin 4) h.fixedField :=
  LinearMap.toMatrix' ((u4HermCoord h).toLinearMap ∘ₗ u4TwistLin h A ∘ₗ
    (u4HermCoord h).symm.toLinearMap)

theorem u4TwistMat_mulVec (A : Matrix (Fin 2) (Fin 2) K) (X : ↥(u4Herm h)) :
    u4TwistMat h A *ᵥ u4HermCoord h X = u4HermCoord h (u4TwistLin h A X) := by
  rw [u4TwistMat, LinearMap.toMatrix'_mulVec]
  simp

theorem eq_of_forall_mulVec_u4HermCoord {M N : Matrix (Fin 4) (Fin 4) h.fixedField}
    (hMN : ∀ X : ↥(u4Herm h), M *ᵥ u4HermCoord h X = N *ᵥ u4HermCoord h X) : M = N := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  obtain ⟨X, rfl⟩ := (u4HermCoord h).surjective v
  exact hMN X

theorem u4TwistMat_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    u4TwistMat h (A * B) = u4TwistMat h A * u4TwistMat h B := by
  refine eq_of_forall_mulVec_u4HermCoord h fun X => ?_
  rw [← Matrix.mulVec_mulVec, u4TwistMat_mulVec, u4TwistMat_mulVec, u4TwistMat_mulVec,
    u4TwistLin_mul, LinearMap.comp_apply]

theorem u4TwistMat_one : u4TwistMat h 1 = 1 := by
  refine eq_of_forall_mulVec_u4HermCoord h fun X => ?_
  rw [u4TwistMat_mulVec, u4TwistLin_one, LinearMap.id_apply, Matrix.one_mulVec]

@[expose] noncomputable def u4TwistMatHom :
    Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 4) (Fin 4) h.fixedField where
  toFun := u4TwistMat h
  map_one' := u4TwistMat_one h
  map_mul' := u4TwistMat_mul h

@[expose] noncomputable def u4TwistHom : GL (Fin 2) K →* GL (Fin 4) h.fixedField :=
  Units.map (u4TwistMatHom h)

theorem coe_u4TwistHom (A : GL (Fin 2) K) :
    ((u4TwistHom h A : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField) =
      u4TwistMat h A :=
  rfl

@[expose] def u4DetFixGL : Subgroup (GL (Fin 2) K) where
  carrier := {A | h.bar (A : Matrix (Fin 2) (Fin 2) K).det = (A : Matrix (Fin 2) (Fin 2) K).det}
  mul_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, map_mul, hA, hB]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.det_one, map_one]
  inv_mem' {A} hA := by
    simp only [Set.mem_setOf_eq] at hA ⊢
    have e : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
        (A : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.det_one]
    rw [eq_inv_of_mul_eq_one_left e, map_inv₀, hA]

theorem mem_u4DetFixGL {A : GL (Fin 2) K} :
    A ∈ u4DetFixGL h ↔
      h.bar (A : Matrix (Fin 2) (Fin 2) K).det = (A : Matrix (Fin 2) (Fin 2) K).det :=
  Iff.rfl

@[expose] noncomputable def u4Gamma2 : Subgroup (GL (Fin 4) h.fixedField) :=
  (u4DetFixGL h).map (u4TwistHom h)

theorem u4TwistHom_mem_u4Gamma2 {A : GL (Fin 2) K} (hA : A ∈ u4DetFixGL h) :
    u4TwistHom h A ∈ u4Gamma2 h :=
  Subgroup.mem_map_of_mem _ hA

theorem mem_u4Gamma2_iff {M : GL (Fin 4) h.fixedField} :
    M ∈ u4Gamma2 h ↔ ∃ A : GL (Fin 2) K,
      h.bar (A : Matrix (Fin 2) (Fin 2) K).det = (A : Matrix (Fin 2) (Fin 2) K).det ∧
        ∀ X : ↥(u4Herm h), (M : Matrix (Fin 4) (Fin 4) h.fixedField) *ᵥ u4HermCoord h X =
          u4HermCoord h (u4TwistLin h (A : Matrix (Fin 2) (Fin 2) K) X) := by
  rw [u4Gamma2, Subgroup.mem_map]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, fun X => u4TwistMat_mulVec h _ X⟩
  · rintro ⟨A, hA, hM⟩
    refine ⟨A, hA, Units.ext ?_⟩
    rw [coe_u4TwistHom]
    exact eq_of_forall_mulVec_u4HermCoord h fun X => by rw [u4TwistMat_mulVec, hM]

theorem eq_one_of_forall_twist_eq {A : Matrix (Fin 2) (Fin 2) K} (hA : h.bar A.det = A.det)
    (hfix : ∀ X ∈ u4Herm h, A * X * (A.map h.bar)ᵀ = X) : A = 1 := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have triple : ∀ (X : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2), (A * X * (A.map h.bar)ᵀ) i j =
      A i 0 * X 0 0 * h.bar (A j 0) + A i 0 * X 0 1 * h.bar (A j 1) +
        A i 1 * X 1 0 * h.bar (A j 0) + A i 1 * X 1 1 * h.bar (A j 1) := by
    intro X i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply]
    ring
  have hE11 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) ∈ u4Herm h := by
    rw [mem_u4Herm]
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hE22 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) ∈ u4Herm h := by
    rw [mem_u4Herm]
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hW : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) ∈ u4Herm h := by
    rw [mem_u4Herm]
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have e1 := hfix _ hE11
  have e2 := hfix _ hE22
  have e3 := hfix _ hW
  have ent : ∀ (X : Matrix (Fin 2) (Fin 2) K), A * X * (A.map h.bar)ᵀ = X → ∀ i j,
      A i 0 * X 0 0 * h.bar (A j 0) + A i 0 * X 0 1 * h.bar (A j 1) +
        A i 1 * X 1 0 * h.bar (A j 0) + A i 1 * X 1 1 * h.bar (A j 1) = X i j := by
    intro X hX i j
    rw [← triple X i j, hX]
  have a00 : A 0 0 * h.bar (A 0 0) = 1 := by
    have := ent _ e1 0 0
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    linear_combination this
  have c0 : A 1 0 * h.bar (A 1 0) = 0 := by
    have := ent _ e1 1 1
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    linear_combination this
  have b0 : A 0 1 * h.bar (A 0 1) = 0 := by
    have := ent _ e2 0 0
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    linear_combination this
  have hc : A 1 0 = 0 := by
    rcases mul_eq_zero.mp c0 with hc | hc
    · exact hc
    · exact (map_eq_zero h.bar).mp hc
  have hb : A 0 1 = 0 := by
    rcases mul_eq_zero.mp b0 with hb | hb
    · exact hb
    · exact (map_eq_zero h.bar).mp hb
  have ad : A 0 0 * h.bar (A 1 1) = 1 := by
    have := ent _ e3 0 1
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hb, hc] at this
    linear_combination this
  have ha0 : A 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one a00
  have hd : A 1 1 = A 0 0 := by
    apply h.bar.injective
    exact mul_left_cancel₀ ha0 (ad.trans a00.symm)
  have hdet : A.det = A 0 0 * A 0 0 := by
    rw [Matrix.det_fin_two, hb, hc, hd]
    ring
  have hbar : h.bar (A 0 0) = A 0 0 := by
    rw [hdet, map_mul] at hA
    have hsq : (h.bar (A 0 0) - A 0 0) ^ 2 = 0 := by
      linear_combination hA + (A 0 0 * A 0 0 - h.bar (A 0 0) * A 0 0) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  have ha1 : A 0 0 = 1 := by
    have haa : A 0 0 * A 0 0 = 1 := by rw [← a00, hbar]
    have hsq : (A 0 0 - 1) ^ 2 = 0 := by
      linear_combination haa + (1 - A 0 0) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [ha1]
  · simp [hb]
  · simp [hc]
  · simp [hd, ha1]

theorem eq_one_of_u4TwistHom_eq_one {A : GL (Fin 2) K} (hA : A ∈ u4DetFixGL h)
    (h1 : u4TwistHom h A = 1) : A = 1 := by
  apply Units.ext
  refine eq_one_of_forall_twist_eq h hA fun X hX => ?_
  have e := u4TwistMat_mulVec h (A : Matrix (Fin 2) (Fin 2) K) ⟨X, hX⟩
  rw [← coe_u4TwistHom, h1, Units.val_one, Matrix.one_mulVec] at e
  exact congrArg Subtype.val ((u4HermCoord h).injective e).symm

end CFSG.Quasithin.F112R.St84

end
