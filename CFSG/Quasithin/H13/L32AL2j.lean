module

public import CFSG.Quasithin.EmptyFaithful.S1565L16
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

section Mat2

variable {F : Type} [Field F]

theorem mat_sq_eq (g : Matrix (Fin 2) (Fin 2) F) :
    g * g = Matrix.trace g • g - g.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem eq_zero_of_mul_eq (h2 : (2 : F) = 0) {g : Matrix (Fin 2) (Fin 2) F} (hdet : g.det = 1)
    {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) (hg1 : g ≠ 1) {X : Matrix (Fin 2) (Fin 2) F}
    (hX : g * X = X) : X = 0 := by
  by_contra hX0
  have hsq := mat_sq_eq g
  have h1 : (g * g) * X = X := by rw [Matrix.mul_assoc, hX, hX]
  rw [hsq, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hX, hdet, one_smul,
    Matrix.one_mul] at h1
  have htrX : Matrix.trace g • X = 0 := by
    have e : Matrix.trace g • X = X + X := sub_eq_iff_eq_add.mp h1
    rw [e, ← two_smul F X, h2, zero_smul]
  have htr : Matrix.trace g = 0 := by
    by_contra h
    apply hX0
    have := congrArg ((Matrix.trace g)⁻¹ • ·) htrX
    simpa [smul_smul, inv_mul_cancel₀ h] using this
  have hg2 : g * g = 1 := by
    rw [hsq, htr, zero_smul, zero_sub, hdet, one_smul]
    have : (1 : Matrix (Fin 2) (Fin 2) F) + 1 = 0 := by
      rw [← two_smul F (1 : Matrix (Fin 2) (Fin 2) F), h2, zero_smul]
    rw [neg_eq_iff_add_eq_zero, this]
  obtain ⟨k, rfl⟩ := hm
  apply hg1
  calc g = (g * g) ^ k * g := by rw [hg2, one_pow, one_mul]
    _ = g ^ (2 * k + 1) := by rw [pow_succ, pow_mul, sq]
    _ = 1 := hgm

end Mat2

section Tensor

variable {W' : Type} [CommGroup W'] {F : Type} [Field F] {Mp : Subgroup (MulAut W')}
  {π : TensorG2 F →* ↥Mp} {β : W' ≃* TensorE2 F}

theorem det_eq_one (g : ↥(StatedSL 2 F)) :
    ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  (CFSG.Semidihedral.ProjectiveSL2Cover.mem_statedSL_iff_det_eq_one F 2 g).mp g.2

theorem tensor_apply (hd : IsTensorData2 Mp π β) (γ : TensorG2 F) (w : W') :
    Multiplicative.toAdd (β ((π γ : MulAut W') w)) =
      ((γ.1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (β w) *
        ((γ.2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  rw [hd γ w]
  rfl

theorem fix_eq_one_left (h2 : (2 : F) = 0) (hd : IsTensorData2 Mp π β) {g : ↥(StatedSL 2 F)}
    {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) (hg1 : g ≠ 1) {w : W'}
    (hw : (π (g, 1) : MulAut W') w = w) : w = 1 := by
  have h1 := tensor_apply hd (g, 1) w
  rw [hw] at h1
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one] at h1
  have hX := eq_zero_of_mul_eq h2 (det_eq_one g) hm
    (by
      have := congrArg (fun x : ↥(StatedSL 2 F) => ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
        hgm
      simpa using this)
    (fun h => hg1 (Subtype.ext (Units.ext h))) h1.symm
  apply β.injective
  rw [map_one]
  exact Multiplicative.toAdd.injective (by rw [hX]; rfl)

theorem fix_eq_one_right (h2 : (2 : F) = 0) (hd : IsTensorData2 Mp π β) {g : ↥(StatedSL 2 F)}
    {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) (hg1 : g ≠ 1) {w : W'}
    (hw : (π (1, g) : MulAut W') w = w) : w = 1 := by
  have h1 := tensor_apply hd (1, g) w
  rw [hw] at h1
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mul] at h1
  have h1' : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (Multiplicative.toAdd (β w))ᵀ = (Multiplicative.toAdd (β w))ᵀ := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, eq_comm] at this
  have hX := eq_zero_of_mul_eq h2 (det_eq_one g) hm
    (by
      have := congrArg (fun x : ↥(StatedSL 2 F) => ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
        hgm
      simpa using this)
    (fun h => hg1 (Subtype.ext (Units.ext h))) h1'
  apply β.injective
  rw [map_one]
  have : Multiplicative.toAdd (β w) = 0 := by
    have := congrArg Matrix.transpose hX
    rwa [Matrix.transpose_transpose, Matrix.transpose_zero] at this
  exact Multiplicative.toAdd.injective (by rw [this]; rfl)

end Tensor

section Span

variable {F : Type} [Field F]

@[expose] noncomputable def slOf (M : Matrix (Fin 2) (Fin 2) F) (h : M.det = 1) : ↥(StatedSL 2 F) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [h]; exact one_ne_zero),
    (CFSG.Semidihedral.ProjectiveSL2Cover.mem_statedSL_iff_det_eq_one F 2 _).mpr (by simpa using h)⟩

theorem slOf_coe (M : Matrix (Fin 2) (Fin 2) F) (h : M.det = 1) :
    ((slOf M h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = M := rfl

theorem exists_four (h2 : (2 : F) = 0) (X : Matrix (Fin 2) (Fin 2) F) :
    ∃ g₁ g₂ g₃ g₄ : ↥(StatedSL 2 F), X = ((g₁ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ +
      ((g₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ +
      ((g₃ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ +
      ((g₄ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  have hneg : (-1 : F) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  refine ⟨slOf !![X 0 0, 1; 1, 0] (by simp [Matrix.det_fin_two, hneg]),
    slOf !![0, 1; 1, X 1 1] (by simp [Matrix.det_fin_two, hneg]),
    slOf !![1, 0; X 0 1, 1] (by simp [Matrix.det_fin_two]),
    slOf !![1, X 1 0; 0, 1] (by simp [Matrix.det_fin_two]), ?_⟩
  simp only [slOf_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply] <;>
    first
    | linear_combination h2
    | linear_combination -h2

end Span

section Tensor2

variable {W' : Type} [CommGroup W'] {F : Type} [Field F] {Mp : Subgroup (MulAut W')}
  {π : TensorG2 F →* ↥Mp} {β : W' ≃* TensorE2 F}

@[expose] noncomputable def matOf (β : W' ≃* TensorE2 F) (f : MulAut W') :
    Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F where
  toFun X := Multiplicative.toAdd (β (f (β.symm (Multiplicative.ofAdd X))))
  map_zero' := by simp
  map_add' X Y := by simp [ofAdd_add]

theorem matOf_apply (f : MulAut W') (w : W') :
    matOf β f (Multiplicative.toAdd (β w)) = Multiplicative.toAdd (β (f w)) := by
  simp [matOf]

theorem matOf_injective (f : MulAut W') : Function.Injective (matOf β f) := by
  intro X Y h
  have h1 : β (f (β.symm (Multiplicative.ofAdd X))) = β (f (β.symm (Multiplicative.ofAdd Y))) :=
    Multiplicative.toAdd.injective h
  simpa using h1

theorem exists_left_of_comm (h2 : (2 : F) = 0) (hd : IsTensorData2 Mp π β) {f : MulAut W'}
    (hf : ∀ g : ↥(StatedSL 2 F), f * (π (1, g) : MulAut W') = (π (1, g) : MulAut W') * f) :
    ∃ Y : Matrix (Fin 2) (Fin 2) F, ∀ X, matOf β f X = Y * X := by
  have hR : ∀ (g : ↥(StatedSL 2 F)) (X : Matrix (Fin 2) (Fin 2) F),
      matOf β f (X * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ) =
        matOf β f X * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
    intro g X
    have e1 : X * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ =
        Multiplicative.toAdd (β ((π (1, g) : MulAut W') (β.symm (Multiplicative.ofAdd X)))) := by
      rw [tensor_apply hd]
      simp
    have e2 := tensor_apply hd (1, g) (f (β.symm (Multiplicative.ofAdd X)))
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mul] at e2
    rw [e1, matOf_apply, ← MulAut.mul_apply, hf, MulAut.mul_apply, e2]
    rfl
  refine ⟨matOf β f 1, fun X => ?_⟩
  obtain ⟨g₁, g₂, g₃, g₄, rfl⟩ := exists_four h2 X
  have hone : ∀ g : ↥(StatedSL 2 F), matOf β f ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ =
      matOf β f 1 * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ := fun g => by
    rw [← hR g 1, Matrix.one_mul]
  simp only [map_add, Matrix.mul_add, hone]

theorem exists_right_of_comm (h2 : (2 : F) = 0) (hd : IsTensorData2 Mp π β) {f : MulAut W'}
    (hf : ∀ g : ↥(StatedSL 2 F), f * (π (g, 1) : MulAut W') = (π (g, 1) : MulAut W') * f) :
    ∃ Z : Matrix (Fin 2) (Fin 2) F, ∀ X, matOf β f X = X * Z := by
  have hL : ∀ (g : ↥(StatedSL 2 F)) (X : Matrix (Fin 2) (Fin 2) F),
      matOf β f (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * X) =
        ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * matOf β f X := by
    intro g X
    have e1 : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * X =
        Multiplicative.toAdd (β ((π (g, 1) : MulAut W') (β.symm (Multiplicative.ofAdd X)))) := by
      rw [tensor_apply hd]
      simp
    have e2 := tensor_apply hd (g, 1) (f (β.symm (Multiplicative.ofAdd X)))
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one] at e2
    rw [e1, matOf_apply, ← MulAut.mul_apply, hf, MulAut.mul_apply, e2]
    rfl
  refine ⟨matOf β f 1, fun X => ?_⟩
  obtain ⟨g₁, g₂, g₃, g₄, hX⟩ := exists_four h2 Xᵀ
  have hX' : X = ((g₁ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) +
      ((g₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) +
      ((g₃ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) +
      ((g₄ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg Matrix.transpose hX
    simpa using this
  have hone : ∀ g : ↥(StatedSL 2 F), matOf β f ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * matOf β f 1 := fun g => by
    rw [← hL g 1, Matrix.mul_one]
  rw [hX']
  simp only [map_add, Matrix.add_mul, hone]

end Tensor2

section Conj

variable {W' : Type} [CommGroup W'] {F : Type} [Field F] [Finite F] {Mp : Subgroup (MulAut W')}
  {π : TensorG2 F →* ↥Mp} {β : W' ≃* TensorE2 F}

theorem exists_sq_eq (h2 : (2 : F) = 0) (c : F) : ∃ μ : F, μ * μ = c := by
  have hinj : Function.Injective fun x : F => x * x := by
    intro x y hxy
    have h : (x - y) * (x - y) = 0 := by
      have e : (x - y) * (x - y) = x * x - y * y - 2 * x * y + 2 * y * y := by ring
      simp only at hxy
      rw [e, hxy, h2]
      ring
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
  exact (Finite.injective_iff_surjective.mp hinj) c

omit [Finite F] in
theorem det_ne_zero_of_injective {Y : Matrix (Fin 2) (Fin 2) F}
    (h : Function.Injective fun X : Matrix (Fin 2) (Fin 2) F => Y * X) : Y.det ≠ 0 := by
  intro hdet
  have h1 : Y * Y.adjugate = Y * 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul, Matrix.mul_zero]
  have h2 := h h1
  have hY : Y = 0 := by
    rw [Matrix.adjugate_fin_two] at h2
    ext i j
    fin_cases i <;> fin_cases j
    · have := congrFun (congrFun h2 1) 1
      simpa using this
    · have := congrFun (congrFun h2 0) 1
      simpa using this
    · have := congrFun (congrFun h2 1) 0
      simpa using this
    · have := congrFun (congrFun h2 0) 0
      simpa using this
  have h3 : Y * 1 = Y * 0 := by rw [hY, Matrix.zero_mul, Matrix.zero_mul]
  exact one_ne_zero (h h3)

theorem exists_conj_left (h2 : (2 : F) = 0) (hd : IsTensorData2 Mp π β) {f : MulAut W'}
    (hf : ∀ g : ↥(StatedSL 2 F), f * (π (1, g) : MulAut W') = (π (1, g) : MulAut W') * f) :
    ∃ g₀ : ↥(StatedSL 2 F), ∀ g : ↥(StatedSL 2 F),
      f * (π (g, 1) : MulAut W') * f⁻¹ = (π (g₀ * g * g₀⁻¹, 1) : MulAut W') := by
  obtain ⟨Y, hY⟩ := exists_left_of_comm h2 hd hf
  have hinj : Function.Injective fun X : Matrix (Fin 2) (Fin 2) F => Y * X := by
    intro X X' h
    exact matOf_injective (β := β) f (by rw [hY, hY]; exact h)
  have hdet := det_ne_zero_of_injective hinj
  obtain ⟨μ, hμ⟩ := exists_sq_eq h2 Y.det
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hμ, mul_zero])
  have hdet0 : (μ⁻¹ • Y).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hμ]
    field_simp
  refine ⟨slOf (μ⁻¹ • Y) hdet0, fun g => ?_⟩
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hdet
  apply MulEquiv.ext
  intro w
  apply β.injective
  apply Multiplicative.toAdd.injective
  have hZ : Multiplicative.toAdd (β (f⁻¹ w)) = Y⁻¹ * Multiplicative.toAdd (β w) := by
    have h1 := matOf_apply (β := β) f (f⁻¹ w)
    rw [hY, MulAut.apply_inv_self] at h1
    rw [← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hYu, Matrix.one_mul]
  rw [MulAut.mul_apply, MulAut.mul_apply, ← matOf_apply, hY, tensor_apply hd, hZ,
    tensor_apply hd]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.coe_units_inv, slOf_coe,
    OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  have hinv : (μ⁻¹ • Y)⁻¹ = μ • Y⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hμ0, one_smul,
      Matrix.nonsing_inv_mul _ hYu]
  rw [hinv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [mul_inv_cancel₀ hμ0, one_smul]

theorem exists_conj_right (h2 : (2 : F) = 0) (hd : IsTensorData2 Mp π β) {f : MulAut W'}
    (hf : ∀ g : ↥(StatedSL 2 F), f * (π (g, 1) : MulAut W') = (π (g, 1) : MulAut W') * f) :
    ∃ h₀ : ↥(StatedSL 2 F), ∀ h : ↥(StatedSL 2 F),
      f * (π (1, h) : MulAut W') * f⁻¹ = (π (1, h₀ * h * h₀⁻¹) : MulAut W') := by
  obtain ⟨Z, hZ⟩ := exists_right_of_comm h2 hd hf
  have hinj : Function.Injective fun X : Matrix (Fin 2) (Fin 2) F => Zᵀ * X := by
    intro X X' h
    have h1 : Xᵀ * Z = X'ᵀ * Z := by
      have := congrArg Matrix.transpose h
      simpa [Matrix.transpose_mul] using this
    have h3 : Xᵀ = X'ᵀ := matOf_injective (β := β) f (by rw [hZ, hZ]; exact h1)
    have := congrArg Matrix.transpose h3
    simpa using this
  have hdet : Z.det ≠ 0 := by
    have := det_ne_zero_of_injective hinj
    rwa [Matrix.det_transpose] at this
  have hZu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨μ, hμ⟩ := exists_sq_eq h2 Z.det
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hμ, mul_zero])
  have hdet0 : (μ⁻¹ • Zᵀ).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_transpose, ← hμ]
    field_simp
  refine ⟨slOf (μ⁻¹ • Zᵀ) hdet0, fun h => ?_⟩
  apply MulEquiv.ext
  intro w
  apply β.injective
  apply Multiplicative.toAdd.injective
  have hW : Multiplicative.toAdd (β (f⁻¹ w)) = Multiplicative.toAdd (β w) * Z⁻¹ := by
    have h1 := matOf_apply (β := β) f (f⁻¹ w)
    rw [hZ, MulAut.apply_inv_self] at h1
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZu, Matrix.mul_one]
  rw [MulAut.mul_apply, MulAut.mul_apply, ← matOf_apply, hZ, tensor_apply hd, hW,
    tensor_apply hd]
  have hinv : (μ⁻¹ • Zᵀ)⁻¹ = μ • (Zᵀ)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hμ0, one_smul,
      Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose])]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.coe_units_inv, slOf_coe,
    OneMemClass.coe_one, Units.val_one, Matrix.one_mul, hinv, Matrix.transpose_mul,
    Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [inv_mul_cancel₀ hμ0, one_smul]

end Conj

end CFSG.Quasithin.H13.L32A.L2
