module

public import CFSG.Quasithin.H13.KGLieTwSL3
public import CFSG.Quasithin.H13.KGLieTwRank
public import CFSG.Quasithin.H13.KGLieSL3Four

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open scoped Matrix

section NineTwo

variable {F : Type} [Field F] [CharP F 2]

@[expose] def soc3 : Set (Matrix (Fin 3) (Fin 3) F) :=
  {Y | ∃ c b : F, (c = 0 ∨ c = 1) ∧ Y = c • unitM 0 + hermOff 1 0 1 b}

theorem hermOff_add (a : ℕ) {ι : Type} [DecidableEq ι] (i j : ι) (b b' : F) :
    hermOff a i j (b + b') = hermOff a i j b + hermOff a i j b' := by
  simp only [hermOff, add_pow_char_pow, Matrix.single_add]
  abel

theorem soc3_add {Y Y' : Matrix (Fin 3) (Fin 3) F} (hY : Y ∈ soc3) (hY' : Y' ∈ soc3) :
    Y + Y' ∈ soc3 := by
  obtain ⟨c, b, hc, rfl⟩ := hY
  obtain ⟨c', b', hc', rfl⟩ := hY'
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine ⟨c + c', b + b', ?_, ?_⟩
  · rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
    · left; ring
    · right; ring
    · right; ring
    · left; linear_combination h2
  · rw [hermOff_add, add_smul]
    abel

omit [CharP F 2] in
theorem soc_usl3 (Y : Matrix (Fin 3) (Fin 3) F) (hY : IsHerm 1 Y)
    (hs : ∀ u ∈ usl3 F,
      twist 1 (((u : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) Y - Y = 0 ∨
      twist 1 (((u : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) Y - Y = unitM 0) :
    Y ∈ soc3 := by
  have hH : ∀ i j, Y j i ^ 2 ^ 1 = Y i j := fun i j => by
    have := congrFun (congrFun hY i) j
    simpa [frobPow] using this
  have hoff : ∀ (p q r : F) (i j : Fin 3), ¬ (i = 0 ∧ j = 0) →
      (twist 1 (uMat p q r) Y - Y) i j = 0 := by
    intro p q r i j hij
    rcases hs _ (uMat_mem_usl3 p q r) with h | h <;> rw [coe_uSL_stated] at h <;> rw [h]
    · rfl
    · have e : ¬ ((0 : Fin 3) = i ∧ (0 : Fin 3) = j) := fun h' => hij ⟨h'.1.symm, h'.2.symm⟩
      simp [unitM, e]
  have a01 := hoff 1 0 0 0 1 (by decide)
  have a02 := hoff 1 0 0 0 2 (by decide)
  have a20 := hoff 1 0 0 2 0 (by decide)
  have c10 := hoff 0 0 1 1 0 (by decide)
  have c12 := hoff 0 0 1 1 2 (by decide)
  have c01 := hoff 0 0 1 0 1 (by decide)
  simp only [Matrix.sub_apply, twist_apply, Fin.sum_univ_three, uMat_00, uMat_01, uMat_02,
    uMat_10, uMat_11, uMat_12, uMat_20, uMat_21, uMat_22, one_pow, zero_pow two_ne_zero,
    pow_one, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] at a01 a02 a20 c10 c12 c01
  have y11 : Y 1 1 = 0 := by linear_combination a01
  have y12 : Y 1 2 = 0 := by linear_combination a02
  have y21 : Y 2 1 = 0 := by linear_combination a20
  have y20 : Y 2 0 = 0 := by linear_combination c10
  have y22 : Y 2 2 = 0 := by linear_combination c12
  have y02 : Y 0 2 = 0 := by linear_combination c01
  have hd := isHerm_diag hY 0
  refine ⟨Y 0 0, Y 0 1, ?_, ?_⟩
  · have : Y 0 0 * (Y 0 0 - 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unitM, hermOff, y11, y12, y21, y20, y22, y02, ← hH 1 0]

theorem supp_sl3 [Finite F] (hF : Nat.card F = 2 ^ (2 * 1)) (γ : ↥(StatedSL 3 F))
    (hγ : ∀ X, IsHerm 1 X →
      twist 1 ((γ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) X - X ∈ soc3) :
    ∀ X, IsHerm 1 X →
      twist 1 ((γ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) X = X := by
  set g : Matrix (Fin 3) (Fin 3) F :=
    ((γ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hg
  have hz : ∀ X, IsHerm 1 X → ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 0) → ¬ (i = 0 ∧ j = 1) →
      ¬ (i = 1 ∧ j = 0) → (twist 1 g X - X) i j = 0 := by
    intro X hX i j h00 h01 h10
    obtain ⟨c, b, -, hcb⟩ := hγ X hX
    rw [hcb]
    have e1 : ¬ ((0 : Fin 3) = i ∧ (0 : Fin 3) = j) := fun h => h00 ⟨h.1.symm, h.2.symm⟩
    have e2 : ¬ ((0 : Fin 3) = i ∧ (1 : Fin 3) = j) := fun h => h01 ⟨h.1.symm, h.2.symm⟩
    have e3 : ¬ ((1 : Fin 3) = i ∧ (0 : Fin 3) = j) := fun h => h10 ⟨h.1.symm, h.2.symm⟩
    simp [unitM, hermOff, e1, e2, e3]
  have hE : ∀ i : Fin 3, IsHerm 1 (unitM i : Matrix (Fin 3) (Fin 3) F) := isHerm_unitM 1
  have hO : ∀ i j : Fin 3, IsHerm 1 (hermOff 1 i j (1 : F)) := fun i j => isHerm_hermOff hF i j 1
  have e22 := fun i j h1 h2 h3 => hz _ (hE 2) i j h1 h2 h3
  have e11 := fun i j h1 h2 h3 => hz _ (hE 1) i j h1 h2 h3
  have e00 := fun i j h1 h2 h3 => hz _ (hE 0) i j h1 h2 h3
  have e12 := fun i j h1 h2 h3 => hz _ (hO 1 2) i j h1 h2 h3
  have e02 := fun i j h1 h2 h3 => hz _ (hO 0 2) i j h1 h2 h3
  have a22 := e22 2 2 (by decide) (by decide) (by decide)
  have a11 := e22 1 1 (by decide) (by decide) (by decide)
  have a02 := e22 0 2 (by decide) (by decide) (by decide)
  have b22 := e11 2 2 (by decide) (by decide) (by decide)
  have b11 := e11 1 1 (by decide) (by decide) (by decide)
  have c11 := e00 1 1 (by decide) (by decide) (by decide)
  have c22 := e00 2 2 (by decide) (by decide) (by decide)
  have d12 := e12 1 2 (by decide) (by decide) (by decide)
  have d02 := e12 0 2 (by decide) (by decide) (by decide)
  have f02 := e02 0 2 (by decide) (by decide) (by decide)
  simp only [Matrix.sub_apply, twist_apply, Fin.sum_univ_three, unitM, hermOff,
    Matrix.single_apply] at a22 a11 a02 b22 b11 c11 c22 d12 d02 f02
  simp at a22 a11 a02 b22 b11 c11 c22 d12 d02 f02
  have hμ : g 2 2 * g 2 2 ^ 2 = 1 := by linear_combination a22
  have h22 : g 2 2 ≠ 0 := by
    intro h0
    rw [h0] at hμ
    simp at hμ
  have h02 : g 0 2 = 0 := a02.resolve_right h22
  have h2sq : g 2 2 ^ 2 ≠ 0 := pow_ne_zero 2 h22
  have h11 : g 1 1 = g 2 2 := by
    have : (g 1 1 - g 2 2) * g 2 2 ^ 2 = 0 := by
      rw [a11] at d12
      linear_combination d12 - hμ
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2sq)
  have h00 : g 0 0 = g 2 2 := by
    have : (g 0 0 - g 2 2) * g 2 2 ^ 2 = 0 := by
      rw [h02] at f02
      linear_combination f02 - hμ
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2sq)
  have h01 : g 0 1 = 0 := by
    rw [h02] at d02
    have : g 0 1 * g 2 2 ^ 2 = 0 := by linear_combination d02
    exact (mul_eq_zero.mp this).resolve_right h2sq
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = g 2 2 := ⟨_, rfl⟩
  rw [← hμd] at hμ h11 h00
  have hgμ : g = μ • (1 : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h11, h00, h01, h02, a11, b22, c11, c22, hμd]
  intro X hX
  rw [hgμ, twist, frobPow_smul, frobPow_one, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_one,
    show μ ^ 2 * μ = 1 by linear_combination hμ, one_smul]

section Torus

variable {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
include hω

omit [CharP F 2] in
theorem omega_cube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω

omit [CharP F 2] in
theorem tor3_mul_inv : Matrix.diagonal ![ω, ω ^ 2, 1] * Matrix.diagonal ![ω ^ 2, ω, 1] =
    (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp
  · linear_combination omega_cube hω
  · linear_combination omega_cube hω

omit [CharP F 2] in
theorem tor3_inv_mul : Matrix.diagonal ![ω ^ 2, ω, 1] * Matrix.diagonal ![ω, ω ^ 2, 1] =
    (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp
  · linear_combination omega_cube hω
  · linear_combination omega_cube hω

omit [CharP F 2] in
theorem det_tor3 : (Matrix.diagonal ![ω, ω ^ 2, 1] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp
  linear_combination omega_cube hω

@[expose] def tor3 : ↥(StatedSL 3 F) :=
  ⟨⟨Matrix.diagonal ![ω, ω ^ 2, 1], Matrix.diagonal ![ω ^ 2, ω, 1], tor3_mul_inv hω,
    tor3_inv_mul hω⟩, Subgroup.subset_closure (det_tor3 hω)⟩

omit [CharP F 2] in
theorem twist_tor3 (c b : F) :
    twist 1 (((tor3 hω : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) (c • unitM 0 + hermOff 1 0 1 b) =
      c • unitM 0 + hermOff 1 0 1 (ω ^ 2 * b) := by
  have h3 := omega_cube hω
  show twist 1 (Matrix.diagonal ![ω, ω ^ 2, 1]) _ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Matrix.diagonal_apply, unitM, hermOff, Matrix.single_apply]
  · linear_combination c * h3
  · linear_combination (ω ^ 2 * b) * h3
  · ring

omit [CharP F 2] in
theorem tor3_soc3 {Y : Matrix (Fin 3) (Fin 3) F} (hY : Y ∈ soc3) :
    twist 1 (((tor3 hω : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) Y ∈ soc3 := by
  obtain ⟨c, b, hc, rfl⟩ := hY
  exact ⟨c, ω ^ 2 * b, hc, twist_tor3 hω c b⟩

omit [CharP F 2] in
theorem tor3_E00 :
    twist 1 (((tor3 hω : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) (unitM 0) = unitM 0 := by
  have h := twist_tor3 hω 1 0
  simpa [hermOff] using h

theorem tor3_move {Y : Matrix (Fin 3) (Fin 3) F} (hY : Y ∈ soc3)
    (h : twist 1 (((tor3 hω : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) Y = Y ∨
      twist 1 (((tor3 hω : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) Y = Y + unitM 0) :
    Y = 0 ∨ Y = unitM 0 := by
  obtain ⟨c, b, hc, rfl⟩ := hY
  rw [twist_tor3] at h
  have hb : b = 0 := by
    have e : ω ^ 2 * b = b := by
      rcases h with h | h
      · have := congrFun (congrFun h 0) 1
        simpa [unitM, hermOff, Matrix.single_apply] using this
      · have := congrFun (congrFun h 0) 1
        simpa [unitM, hermOff, Matrix.single_apply] using this
    have hω1 : ω ^ 2 - 1 ≠ 0 := by
      intro h0
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have : (1 : F) = 0 := by linear_combination ω * hω - (ω + 1) * h0 - ω * h2
      exact one_ne_zero this
    have : (ω ^ 2 - 1) * b = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left hω1
  subst hb
  rcases hc with rfl | rfl
  · left
    simp [hermOff]
  · right
    simp [hermOff]

end Torus

end NineTwo

section Row

variable {V : Type} [CommGroup V] [Finite V]

theorem factLieNineTwoRow1321_holds : A5.FactLieNineTwoRow1321 := by
  intro V _ _ hV2 G L v hB4 hc h
  obtain ⟨F, _, _, _, hF, hr⟩ := h
  have hF' : Nat.card F = 2 ^ (2 * 1) := hF
  have hK4 : Nat.card F = 4 := by rw [hF']; norm_num
  obtain ⟨ω, hω⟩ := exists_omega hK4
  obtain ⟨T, hT⟩ := exists_twData hV2 hB4 hc hF' (usl3 F) (isPGroup_usl3 hF')
    (not_dvd_index_usl3 hF' (by norm_num)) (Or.inl rfl) hr
  exact false_of_twData hF' (Or.inl rfl) det_stated3 (isPGroup_usl3 hF') (hi := 0) (lo := 2)
    (by decide) (fix_usl3 le_rfl hF') (chi_usl3 le_rfl hF') (wsl3 F) (twist_wsl3_E00 1)
    (twist_wsl3_one 1) hT (fun _ => rank_one_of_socle hF' (isPGroup_usl3 hF')
      (fix_usl3 le_rfl hF') soc3 (fun _ _ => soc3_add) soc_usl3 (supp_sl3 hF') (tor3 hω)
      (fun _ hY => tor3_soc3 hω hY) (tor3_E00 hω) (fun _ hY h => tor3_move hω hY h) hT)

end Row

end CFSG.Quasithin.H13.KGLie
