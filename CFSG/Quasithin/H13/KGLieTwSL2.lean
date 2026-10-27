module

public import CFSG.Quasithin.H13.KGLieTwDet

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup CFSG.CGT.Timmesfeld75
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open scoped Matrix MatrixGroups

section SL2

variable {F : Type} [Field F] [CharP F 2]

variable (F) in
@[expose] noncomputable def ut2 : Subgroup ↥(StatedSL 2 F) :=
  (utri F).map (specialLinearGroupEquivStatedSL 2 F).toMonoidHom

omit [CharP F 2] in
theorem utriElt_mem_ut2 (t : F) : specialLinearGroupEquivStatedSL 2 F (utriElt t) ∈ ut2 F :=
  Subgroup.mem_map_of_mem _ (utriElt_mem_utri t)

theorem isPGroup_ut2 [Finite F] : IsPGroup 2 (ut2 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isPGroup_utri.map _

theorem not_dvd_index_ut2 [Finite F] : ¬ 2 ∣ (ut2 F).index := by
  rw [ut2, Subgroup.index_map_of_bijective (specialLinearGroupEquivStatedSL 2 F).bijective,
    ← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact odd_index_utri

omit [CharP F 2] in
theorem det_stated2 (γ : ↥(StatedSL 2 F)) :
    ((γ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective γ
  rw [specialLinearGroupEquivStatedSL_coe]
  exact A.2

omit [CharP F 2] in
theorem coe_utriElt_stated (t : F) :
    (((specialLinearGroupEquivStatedSL 2 F (utriElt t) : ↥(StatedSL 2 F)) :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  rw [specialLinearGroupEquivStatedSL_coe]
  ext i j
  fin_cases i <;> fin_cases j
  · exact utriElt_apply_00 t
  · exact utriElt_apply_01 t
  · exact utriElt_apply_10 t
  · exact utriElt_apply_11 t

theorem fix_ut2 [Finite F] {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (X : Matrix (Fin 2) (Fin 2) F) (_hX : IsHerm a X)
    (hfix : ∀ u ∈ ut2 F,
      twist a (((u : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) X = X) :
    X = X 0 0 • unitM 0 := by
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨θ, hθ⟩ := exists_frob_ne ha hF
  have hp : 2 ^ a ≠ 0 := by positivity
  have h1 : ∀ t : F, twist a !![1, t; 0, 1] X = X := fun t => by
    have := hfix _ (utriElt_mem_ut2 t)
    rwa [coe_utriElt_stated] at this
  have e := fun t i j => congrFun (congrFun (h1 t) i) j
  have a01 := e 1 0 1
  have a00 := e 1 0 0
  have b00 := e θ 0 0
  simp [twist_apply, Fin.sum_univ_two] at a01 a00 b00
  have x11 : X 1 1 = 0 := by linear_combination a01
  have x01 : X 0 1 = X 1 0 := by linear_combination a00 - x11 - X 1 0 * h2F
  have x10 : X 1 0 = 0 := by
    have h3 : X 1 0 * (θ + θ ^ 2 ^ a) = 0 := by
      linear_combination b00 - (θ * θ ^ 2 ^ a) * x11 - θ ^ 2 ^ a * x01
    exact (mul_eq_zero.mp h3).resolve_right (trc_ne_zero hθ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitM, x11, x01, x10]

omit [CharP F 2] in
theorem twist_u2_E11 (a : ℕ) (t : F) :
    twist a !![1, t; 0, 1] (unitM 1) = unitM 1 + nrm a t • unitM 0 + hermOff a 0 1 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fin.sum_univ_two, unitM, hermOff, Matrix.single_apply, nrm]

omit [CharP F 2] in
theorem herm_decomp2 {a : ℕ} {X : Matrix (Fin 2) (Fin 2) F} (hX : IsHerm a X) :
    X = X 0 0 • unitM 0 + X 1 1 • unitM 1 + hermOff a 0 1 (X 0 1) := by
  have hH : ∀ i j, X j i ^ 2 ^ a = X i j := fun i j => by
    have := congrFun (congrFun hX i) j
    simpa [frobPow] using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOff, unitM, hH]

theorem chi_ut2 [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a))
    (χ : Matrix (Fin 2) (Fin 2) F → F)
    (hadd : ∀ X Y, IsHerm a X → IsHerm a Y → χ (X + Y) = χ X + χ Y)
    (hsmul : ∀ k : F, k ^ 2 ^ a = k → ∀ X, IsHerm a X → χ (k • X) = k * χ X)
    (hU : ∀ u ∈ ut2 F, ∀ X, IsHerm a X →
      χ (twist a (((u : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) X) = χ X)
    (h0 : χ (unitM 0) = 0) :
    χ 1 = χ (unitM 1) ∧ (χ (unitM 1) = 0 → ∀ X, IsHerm a X → χ X = 0) := by
  have hE : ∀ i : Fin 2, IsHerm a (unitM i : Matrix (Fin 2) (Fin 2) F) := isHerm_unitM a
  have hO : ∀ t : F, IsHerm a (hermOff a (0 : Fin 2) 1 t) := fun t => isHerm_hermOff hF 0 1 t
  have hNE : ∀ (i : Fin 2) (t : F), IsHerm a (nrm a t • unitM i : Matrix (Fin 2) (Fin 2) F) :=
    fun i t => isHerm_smul (frob_nrm hF t) (hE i)
  have h01 : ∀ t, χ (hermOff a 0 1 t) = 0 := fun t => by
    have h := hU _ (utriElt_mem_ut2 t) _ (hE 1)
    rw [coe_utriElt_stated, twist_u2_E11, hadd _ _ (isHerm_add (hE 1) (hNE 0 t)) (hO t),
      hadd _ _ (hE 1) (hNE 0 t), hsmul _ (frob_nrm hF t) _ (hE 0), h0, mul_zero,
      add_zero] at h
    linear_combination h
  have hχX : ∀ X, IsHerm a X → χ X = X 1 1 * χ (unitM 1) := by
    intro X hX
    have hd : ∀ i, IsHerm a (X i i • unitM i : Matrix (Fin 2) (Fin 2) F) := fun i =>
      isHerm_smul (isHerm_diag hX i) (hE i)
    conv_lhs => rw [herm_decomp2 hX]
    rw [hadd _ _ (isHerm_add (hd 0) (hd 1)) (hO _), hadd _ _ (hd 0) (hd 1),
      hsmul _ (isHerm_diag hX 0) _ (hE 0), hsmul _ (isHerm_diag hX 1) _ (hE 1), h0, h01]
    ring
  refine ⟨?_, fun h2 X hX => by rw [hχX X hX, h2, mul_zero]⟩
  have h1 := hχX 1 (isHerm_one a)
  simp only [Matrix.one_apply_eq, one_mul] at h1
  exact h1

@[expose] def wMat2 : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

omit [CharP F 2] in
theorem wMat2_mul_self : (wMat2 : Matrix (Fin 2) (Fin 2) F) * wMat2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat2, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_wMat2 : (wMat2 : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp [wMat2, Matrix.det_fin_two]
  linear_combination -h2

variable (F) in
@[expose] def wsl2 : ↥(StatedSL 2 F) :=
  ⟨⟨wMat2, wMat2, wMat2_mul_self, wMat2_mul_self⟩, Subgroup.subset_closure det_wMat2⟩

theorem twist_wsl2_E00 (a : ℕ) :
    twist a (((wsl2 F : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) (unitM 0) = unitM 1 := by
  have hp : 2 ^ a ≠ 0 := by positivity
  show twist a wMat2 (unitM 0) = unitM 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fin.sum_univ_two, wMat2, unitM, Matrix.single_apply]

theorem twist_wsl2_one (a : ℕ) :
    twist a (((wsl2 F : ↥(StatedSL 2 F)) : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  have hp : 2 ^ a ≠ 0 := by positivity
  show twist a wMat2 1 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fin.sum_univ_two, wMat2, Matrix.one_apply]

end SL2

section Row

variable {V : Type} [CommGroup V] [Finite V]

theorem factLieOrthFourRow1321_holds : A5.FactLieOrthFourRow1321 := by
  intro V _ _ hV2 G L v hB4 hc h
  obtain ⟨F, _, _, _, hF, hr⟩ := h
  have hF' : Nat.card F = 2 ^ (2 * 2) := hF
  have h16 : 16 < Nat.card ↥(hermSub 2 (Fin 2) F) := by
    have h1 := card_hermSub_ge hF' (i₀ := (0 : Fin 2)) (i₁ := 1) (by decide)
    have h2 := card_fix_ge hF'
    rw [hF'] at h1
    have h3 : 4 * 4 * 16 ≤ Nat.card {k : F // k ^ 2 ^ 2 = k} *
        Nat.card {k : F // k ^ 2 ^ 2 = k} * 2 ^ (2 * 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul h2 h2) le_rfl
    omega
  obtain ⟨T, hT⟩ := exists_twData hV2 hB4 hc hF' (ut2 F) isPGroup_ut2 not_dvd_index_ut2
    (Or.inr h16) hr
  exact false_of_twData hF' (Or.inr rfl) det_stated2 isPGroup_ut2 (hi := 0) (lo := 1)
    (by decide) (fix_ut2 (by norm_num) hF') (chi_ut2 hF') (wsl2 F) (twist_wsl2_E00 2)
    (twist_wsl2_one 2) hT (fun h => absurd h (by norm_num))

end Row

end CFSG.Quasithin.H13.KGLie
