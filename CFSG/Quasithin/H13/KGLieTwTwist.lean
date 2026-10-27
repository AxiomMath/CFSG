module

public import CFSG.Quasithin.H13.KGLieTwSp4
public import CFSG.Quasithin.H13.KGLieTwRank
public import CFSG.Quasithin.H13.KGLieSL3Four

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped Matrix

section Soc

variable {F : Type} [Field F] [CharP F 2]

@[expose] def soc4 : Set (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :=
  {Y | ∃ c b : F, (c = 0 ∨ c = 1) ∧ Y = c • unitM ie0 + hermOff 1 ie0 ie1 b}

theorem soc4_add {Y Y' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hY : Y ∈ soc4)
    (hY' : Y' ∈ soc4) : Y + Y' ∈ soc4 := by
  obtain ⟨c, b, hc, rfl⟩ := hY
  obtain ⟨c', b', hc', rfl⟩ := hY'
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine ⟨c + c', b + b', ?_, ?_⟩
  · rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
    · left; ring
    · right; ring
    · right; ring
    · left; linear_combination h2
  · simp only [hermOff, add_pow_char_pow, Matrix.single_add, add_smul]
    abel

theorem soc_usp [Finite F] (hF : Nat.card F = 2 ^ (2 * 1))
    (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (hY : IsHerm 1 Y)
    (hs : ∀ u ∈ Usp F,
      twist 1 (((u : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) Y - Y = 0 ∨
      twist 1 (((u : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) Y - Y = unitM ie0) :
    Y ∈ soc4 := by
  have hH : ∀ i j, Y j i ^ 2 ^ 1 = Y i j := fun i j => by
    have := congrFun (congrFun hY i) j
    simpa [frobPow] using this
  have hoff : ∀ (g : ↥(StatedSp 2 F)), g ∈ Usp F → ∀ (i j : Fin 2 ⊕ Fin 2), ¬ (i = ie0 ∧ j = ie0) →
      (twist 1 ((g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) Y - Y) i j = 0 := by
    intro g hg i j hij
    rcases hs g hg with h | h <;> rw [h]
    · rfl
    · have e : ¬ (ie0 = i ∧ ie0 = j) := fun h' => hij ⟨h'.1.symm, h'.2.symm⟩
      simp [unitM, e]
  have hq := fun t i j hij => hoff _ (qSp_mem_Usp' (F := F) t 0 0) i j hij
  have hz := fun t i j hij => hoff _ (qSp_mem_Usp' (F := F) 0 0 t) i j hij
  have hn := fun t i j hij => hoff _ (nSp_mem_Usp' (F := F) t) i j hij
  have q1 := hq 1 ie0 ie1 (by decide)
  have q2 := hq 1 ie0 if0 (by decide)
  have q3 := hq 1 ie0 if1 (by decide)
  have z1 := hz 1 ie1 ie0 (by decide)
  have z2 := hz 1 ie1 if0 (by decide)
  have z3 := hz 1 ie1 if1 (by decide)
  have n1 := hn 1 if1 ie0 (by decide)
  have n2 := hn 1 ie0 ie1 (by decide)
  simp only [mat_qSp', mat_nSp'] at q1 q2 q3 z1 z2 z3 n1 n2
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at q1 q2 q3
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at z1 z2 z3
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, CharTwo.neg_eq] at n1 n2
  obtain ⟨θ, hθ⟩ := exists_frob_ne le_rfl hF
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have z0 := hz θ ie1 ie1 (by decide)
  have z11 := hz 1 ie1 ie1 (by decide)
  simp only [mat_qSp'] at z0 z11
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at z0 z11
  have e13 : Y ie1 if1 = Y if1 ie1 ^ 2 := by rw [← hH ie1 if1]; ring
  rw [e13] at z0 z11
  have hyy : Y if1 ie1 ^ 2 = Y if1 ie1 := by
    linear_combination z11 - z3 - Y if1 ie1 * h2F
  have y31 : Y if1 ie1 = 0 := by
    have h1 : Y if1 ie1 * (θ + θ ^ 2) = 0 := by
      linear_combination z0 - θ * θ ^ 2 * z3 - θ ^ 2 * hyy
    exact (mul_eq_zero.mp h1).resolve_right (trc_ne_zero (a := 1) hθ)
  have y20 : Y if0 ie0 = 0 := by linear_combination n1 - q1 - y31
  have e02 : Y ie0 if0 = 0 := by rw [← hH ie0 if0, y20]; ring
  have e03 : Y ie0 if1 = 0 := by rw [← hH ie0 if1, z1]; ring
  have e12 : Y ie1 if0 = 0 := by rw [← hH ie1 if0, q1]; ring
  have e13' : Y ie1 if1 = 0 := by rw [e13, y31]; ring
  have e10 : Y ie1 ie0 = Y ie0 ie1 ^ 2 ^ 1 := (hH ie1 ie0).symm
  have hd := isHerm_diag hY ie0
  refine ⟨Y ie0 ie0, Y ie0 ie1, ?_, ?_⟩
  · have : Y ie0 ie0 * (Y ie0 ie0 - 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [unitM, hermOff, q1, q2, q3, z1, z2, z3, n2, y31, y20, e02, e03,
        e12, e13', e10]

theorem supp_sp4 [Finite F] (hF : Nat.card F = 2 ^ (2 * 1)) (γ : ↥(StatedSp 2 F))
    (hγ : ∀ X, IsHerm 1 X →
      twist 1 ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) X - X ∈ soc4) :
    ∀ X, IsHerm 1 X → twist 1 ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) X = X := by
  set g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hg
  have hz : ∀ X, IsHerm 1 X → ∀ i j, ¬ (i = ie0 ∧ j = ie0) → ¬ (i = ie0 ∧ j = ie1) →
      ¬ (i = ie1 ∧ j = ie0) → (twist 1 g X - X) i j = 0 := by
    intro X hX i j h00 h01 h10
    obtain ⟨c, b, -, hcb⟩ := hγ X hX
    rw [hcb]
    simp only [Matrix.add_apply, Matrix.smul_apply, unitM, hermOff, Matrix.single_apply]
    have e1 : ¬ (ie0 = i ∧ ie0 = j) := fun h => h00 ⟨h.1.symm, h.2.symm⟩
    have e2 : ¬ (ie0 = i ∧ ie1 = j) := fun h => h01 ⟨h.1.symm, h.2.symm⟩
    have e3 : ¬ (ie1 = i ∧ ie0 = j) := fun h => h10 ⟨h.1.symm, h.2.symm⟩
    simp [e1, e2, e3]
  have hE : ∀ i, IsHerm 1 (unitM i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := isHerm_unitM 1
  have hO : ∀ i j : Fin 2 ⊕ Fin 2, IsHerm 1 (hermOff 1 i j (1 : F)) := fun i j =>
    isHerm_hermOff hF i j 1
  have k3 := fun i j h1 h2 h3 => hz _ (hE if1) i j h1 h2 h3
  have k2 := fun i j h1 h2 h3 => hz _ (hE if0) i j h1 h2 h3
  have k1 := fun i j h1 h2 h3 => hz _ (hE ie1) i j h1 h2 h3
  have k0 := fun i j h1 h2 h3 => hz _ (hE ie0) i j h1 h2 h3
  have o12 := fun i j h1 h2 h3 => hz _ (hO ie1 if0) i j h1 h2 h3
  have o02 := fun i j h1 h2 h3 => hz _ (hO ie0 if0) i j h1 h2 h3
  have o32 := fun i j h1 h2 h3 => hz _ (hO if1 if0) i j h1 h2 h3
  have a33 := k3 if1 if1 (by decide) (by decide) (by decide)
  have a13 := k3 ie1 ie1 (by decide) (by decide) (by decide)
  have a23 := k3 if0 if0 (by decide) (by decide) (by decide)
  have a03 := k3 ie0 if1 (by decide) (by decide) (by decide)
  have b22 := k2 if0 if0 (by decide) (by decide) (by decide)
  have b12 := k2 ie1 ie1 (by decide) (by decide) (by decide)
  have b32 := k2 if1 if1 (by decide) (by decide) (by decide)
  have b02 := k2 ie0 if0 (by decide) (by decide) (by decide)
  have c11 := k1 ie1 ie1 (by decide) (by decide) (by decide)
  have c21 := k1 if0 if0 (by decide) (by decide) (by decide)
  have c31 := k1 if1 if1 (by decide) (by decide) (by decide)
  have d10 := k0 ie1 ie1 (by decide) (by decide) (by decide)
  have d20 := k0 if0 if0 (by decide) (by decide) (by decide)
  have d30 := k0 if1 if1 (by decide) (by decide) (by decide)
  have p02 := o12 ie0 if0 (by decide) (by decide) (by decide)
  have p12 := o12 ie1 if0 (by decide) (by decide) (by decide)
  have r02 := o02 ie0 if0 (by decide) (by decide) (by decide)
  have s32 := o32 if1 if0 (by decide) (by decide) (by decide)
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at a33 a13 a23 a03 b22 b12
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at b32 b02 c11 c21 c31 d10
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at d20 d30 p02 p12 r02 s32
  simp [hermOff] at p02 p12 r02 s32
  have hμ : g if0 if0 * g if0 if0 ^ 2 = 1 := by linear_combination b22
  have hμ0 : g if0 if0 ≠ 0 := by
    intro h0
    rw [h0] at hμ
    simp at hμ
  have h33 : g if1 if1 ≠ 0 := by
    intro h0
    rw [h0] at a33
    simp at a33
  have hsq : g if0 if0 ^ 2 ≠ 0 := pow_ne_zero 2 hμ0
  have x03 : g ie0 if1 = 0 := a03.resolve_right h33
  have x02 : g ie0 if0 = 0 := b02.resolve_right hμ0
  have x01 : g ie0 ie1 = 0 := by
    rw [x02, zero_mul, add_zero] at p02
    exact (mul_eq_zero.mp p02).resolve_right hsq
  have cancel : ∀ x : F, x * g if0 if0 ^ 2 = 1 → x = g if0 if0 := by
    intro x hx
    have : (x - g if0 if0) * g if0 if0 ^ 2 = 0 := by linear_combination hx - hμ
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsq)
  rw [b12, zero_mul, add_zero] at p12
  rw [x02, zero_mul, add_zero] at r02
  rw [b32, zero_mul, zero_add] at s32
  have x11 : g ie1 ie1 = g if0 if0 := cancel _ (by linear_combination p12)
  have x00 : g ie0 ie0 = g if0 if0 := cancel _ (by linear_combination r02)
  have x33 : g if1 if1 = g if0 if0 := cancel _ (by linear_combination s32)
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = g if0 if0 := ⟨_, rfl⟩
  rw [← hμd] at hμ x11 x00 x33
  have hgμ : g = μ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [x00, x01, x02, x03, d10, x11, b12, a13, d20, c21, hμd, a23, d30, c31, b32, x33]
  intro X hX
  rw [hgμ, twist, frobPow_smul, frobPow_one, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_one,
    show μ ^ 2 * μ = 1 by linear_combination hμ, one_smul]

abbrev tor4m (ω : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks (Matrix.diagonal ![ω, 1]) 0 0 (Matrix.diagonal ![ω ^ 2, 1])

omit [CharP F 2] in
theorem tor4m_mul (x y : F) (hxy : x * y = 1) :
    (Matrix.fromBlocks (Matrix.diagonal ![x, 1]) 0 0 (Matrix.diagonal ![y, 1]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
    Matrix.fromBlocks (Matrix.diagonal ![y, 1]) 0 0 (Matrix.diagonal ![x, 1]) = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [← Matrix.fromBlocks_one]
  have hyx : y * x = 1 := by rw [mul_comm]; exact hxy
  congr 1 <;> rw [← Matrix.diagonal_one] <;> congr 1 <;> funext i <;> fin_cases i <;>
    simp [hxy, hyx]


section Torus

variable {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
include hω

omit [CharP F 2] in
theorem omega_cube4 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω

omit [CharP F 2] in
theorem tor4_symp : (tor4m ω)ᵀ * CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2 *
    tor4m ω = CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2 := by
  have h3 := omega_cube4 hω
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, Matrix.diagonal_apply] <;>
    linear_combination h3

@[expose] def tor4 : ↥(StatedSp 2 F) :=
  ⟨⟨tor4m ω, Matrix.fromBlocks (Matrix.diagonal ![ω ^ 2, 1]) 0 0 (Matrix.diagonal ![ω, 1]),
    tor4m_mul ω (ω ^ 2) (by linear_combination omega_cube4 hω),
    tor4m_mul (ω ^ 2) ω (by linear_combination omega_cube4 hω)⟩,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.mem_statedSp_iff.2 (tor4_symp hω)⟩

omit [CharP F 2] in
theorem twist_tor4 (c b : F) :
    twist 1 (((tor4 hω : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (c • unitM ie0 + hermOff 1 ie0 ie1 b) =
      c • unitM ie0 + hermOff 1 ie0 ie1 (ω * b) := by
  have h3 := omega_cube4 hω
  show twist 1 (tor4m ω) _ = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Matrix.diagonal_apply, unitM, hermOff, Matrix.single_apply] <;>
    first | ring1 | linear_combination c * h3

omit [CharP F 2] in
theorem tor4_soc4 {Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hY : Y ∈ soc4) :
    twist 1 (((tor4 hω : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) Y ∈ soc4 := by
  obtain ⟨c, b, hc, rfl⟩ := hY
  exact ⟨c, ω * b, hc, twist_tor4 hω c b⟩

omit [CharP F 2] in
theorem tor4_E :
    twist 1 (((tor4 hω : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (unitM ie0) = unitM ie0 := by
  have h := twist_tor4 hω 1 0
  simpa [hermOff] using h

theorem tor4_move {Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hY : Y ∈ soc4)
    (h : twist 1 (((tor4 hω : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) Y = Y ∨
      twist 1 (((tor4 hω : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) Y = Y + unitM ie0) :
    Y = 0 ∨ Y = unitM ie0 := by
  obtain ⟨c, b, hc, rfl⟩ := hY
  rw [twist_tor4] at h
  have hb : b = 0 := by
    have e : ω * b = b := by
      rcases h with h | h
      · have := congrFun (congrFun h ie0) ie1
        simpa [unitM, hermOff, Matrix.single_apply] using this
      · have := congrFun (congrFun h ie0) ie1
        simpa [unitM, hermOff, Matrix.single_apply] using this
    have hω1 : ω - 1 ≠ 0 := by
      intro h0
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have : (1 : F) = 0 := by linear_combination hω - (ω + 2) * h0 - h2
      exact one_ne_zero this
    have : (ω - 1) * b = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left hω1
  subst hb
  rcases hc with rfl | rfl
  · left
    simp [hermOff]
  · right
    simp [hermOff]

end Torus

end Soc

section Row

variable {V : Type} [CommGroup V] [Finite V]

theorem factLieTwistFourRow1321_holds : A5.FactLieTwistFourRow1321 := by
  intro V _ _ hV2 G L v hB4 hc h
  obtain ⟨F, _, _, _, hF, hr⟩ := h
  have hF' : Nat.card F = 2 ^ (2 * 2) := hF
  have h16 : 16 < Nat.card ↥(hermSub 2 (Fin 2 ⊕ Fin 2) F) := by
    have h1 := card_hermSub_ge hF' (i₀ := ie0) (i₁ := ie1) (by decide)
    have h2 := card_fix_ge hF'
    rw [hF'] at h1
    have h3 : 4 * 4 * 16 ≤ Nat.card {k : F // k ^ 2 ^ 2 = k} *
        Nat.card {k : F // k ^ 2 ^ 2 = k} * 2 ^ (2 * 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul h2 h2) le_rfl
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_twData hV2 hB4 hc hF' (Usp F) (isPGroup_Usp hF')
    (not_dvd_index_Usp hF' (by norm_num)) (Or.inr h16) hr
  exact false_of_twData hF' (Or.inr rfl) det_statedSp (isPGroup_Usp hF') (hi := ie0) (lo := if0)
    (by decide) (fix_usp (by norm_num) hF') (chi_usp (by norm_num) hF') (wsp F)
    (twist_wsp_e0 2) (twist_wsp_one 2) hT (fun h => absurd h (by norm_num))

theorem factLieTwistTwoRow1321_holds : A5.FactLieTwistTwoRow1321 := by
  intro V _ _ hV2 G L v hB4 hc h
  obtain ⟨F, _, _, _, hF, hr⟩ := h
  have hF' : Nat.card F = 2 ^ (2 * 1) := hF
  have hK4 : Nat.card F = 4 := by rw [hF']; norm_num
  obtain ⟨ω, hω⟩ := exists_omega hK4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_twData hV2 hB4 hc hF' (Usp F) (isPGroup_Usp hF')
    (not_dvd_index_Usp hF' (by norm_num)) (Or.inl rfl) hr
  exact false_of_twData hF' (Or.inl rfl) det_statedSp (isPGroup_Usp hF') (hi := ie0) (lo := if0)
    (by decide) (fix_usp le_rfl hF') (chi_usp le_rfl hF') (wsp F) (twist_wsp_e0 1)
    (twist_wsp_one 1) hT (fun _ => rank_one_of_socle hF' (isPGroup_Usp hF')
      (fix_usp le_rfl hF') soc4 (fun _ _ => soc4_add) (soc_usp hF') (supp_sp4 hF') (tor4 hω)
      (fun _ hY => tor4_soc4 hω hY) (tor4_E hω) (fun _ hY h => tor4_move hω hY h) hT)

end Row

end CFSG.Quasithin.H13.KGLie
