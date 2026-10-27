module

public import CFSG.Quasithin.H13.KGLieTwDet
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL3Basic

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open scoped Matrix

section Entries

variable {F : Type} [Field F]

section UMat

variable (p q r : F)

theorem uMat_00 : uMat p q r 0 0 = 1 := rfl
theorem uMat_01 : uMat p q r 0 1 = p := rfl
theorem uMat_02 : uMat p q r 0 2 = q := rfl
theorem uMat_10 : uMat p q r 1 0 = 0 := rfl
theorem uMat_11 : uMat p q r 1 1 = 1 := rfl
theorem uMat_12 : uMat p q r 1 2 = r := rfl
theorem uMat_20 : uMat p q r 2 0 = 0 := rfl
theorem uMat_21 : uMat p q r 2 1 = 0 := rfl
theorem uMat_22 : uMat p q r 2 2 = 1 := rfl

end UMat

end Entries

section SL3

variable {F : Type} [Field F] [CharP F 2]

theorem fix_uMat [Finite F] {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    {X : Matrix (Fin 3) (Fin 3) F} (hX : IsHerm a X)
    (h1 : ∀ t : F, twist a (uMat t 0 0) X = X) (h2 : twist a (uMat 0 0 1) X = X) :
    X = X 0 0 • unitM 0 := by
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨θ, hθ⟩ := exists_frob_ne ha hF
  have hp : 2 ^ a ≠ 0 := by positivity
  have e := fun t i j => congrFun (congrFun (h1 t) i) j
  have e' := fun i j => congrFun (congrFun h2 i) j
  have hH : ∀ i j, X j i ^ 2 ^ a = X i j := fun i j => by
    have := congrFun (congrFun hX i) j
    simpa [frobPow] using this
  have a01 := e 1 0 1
  have a02 := e 1 0 2
  have a21 := e 1 2 0
  have a00 := e 1 0 0
  have b00 := e θ 0 0
  have c10 := e' 1 0
  have c12 := e' 1 2
  have c01 := e' 0 1
  simp only [twist_apply, Fin.sum_univ_three, uMat_00, uMat_01, uMat_02, uMat_10, uMat_11,
    uMat_12, uMat_20, uMat_21, uMat_22, one_pow, zero_pow hp, mul_one, mul_zero, one_mul,
    zero_mul, add_zero, zero_add] at a01 a02 a21 a00 b00 c10 c12 c01
  have x11 : X 1 1 = 0 := by linear_combination a01
  have x12 : X 1 2 = 0 := by linear_combination a02
  have x21 : X 2 1 = 0 := by linear_combination a21
  have x20 : X 2 0 = 0 := by linear_combination c10
  have x22 : X 2 2 = 0 := by linear_combination c12
  have x02 : X 0 2 = 0 := by linear_combination c01
  have x01 : X 0 1 = X 1 0 := by linear_combination a00 - x11 - X 1 0 * h2F
  have x10 : X 1 0 = 0 := by
    have h3 : X 1 0 * (θ + θ ^ 2 ^ a) = 0 := by
      linear_combination b00 - (θ * θ ^ 2 ^ a) * x11 - θ ^ 2 ^ a * x01
    exact (mul_eq_zero.mp h3).resolve_right (trc_ne_zero hθ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitM, x11, x12, x21, x20, x22, x02,
    x01, x10]

omit [CharP F 2] in
theorem twist_x01_E11 (a : ℕ) (t : F) :
    twist a (uMat t 0 0) (unitM 1) = unitM 1 + nrm a t • unitM 0 + hermOff a 0 1 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fin.sum_univ_three, uMat_01, uMat_11,
      uMat_21, unitM, hermOff, Matrix.single_apply, nrm]

omit [CharP F 2] in
theorem twist_x12_E22 (a : ℕ) (t : F) :
    twist a (uMat 0 0 t) (unitM 2) = unitM 2 + nrm a t • unitM 1 + hermOff a 1 2 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fin.sum_univ_three, uMat_02, uMat_12,
      uMat_22, unitM, hermOff, Matrix.single_apply, nrm]

omit [CharP F 2] in
theorem twist_x02_E22 (a : ℕ) (t : F) :
    twist a (uMat 0 t 0) (unitM 2) = unitM 2 + nrm a t • unitM 0 + hermOff a 0 2 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fin.sum_univ_three, uMat_02, uMat_12,
      uMat_22, unitM, hermOff, Matrix.single_apply, nrm]

omit [CharP F 2] in
theorem twist_x12_off12 (a : ℕ) (s t : F) :
    twist a (uMat 0 0 t) (hermOff a 1 2 s) =
      hermOff a 1 2 s + (s * t ^ 2 ^ a + s ^ 2 ^ a * t) • unitM 1 := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fin.sum_univ_three, uMat_00, uMat_01, uMat_02, uMat_10, uMat_11, uMat_12,
      uMat_20, uMat_21, uMat_22, unitM, hermOff, Matrix.single_apply]
  all_goals ring

omit [CharP F 2] in
theorem herm_decomp3 {a : ℕ} {X : Matrix (Fin 3) (Fin 3) F} (hX : IsHerm a X) :
    X = X 0 0 • unitM 0 + X 1 1 • unitM 1 + X 2 2 • unitM 2 + hermOff a 0 1 (X 0 1) +
      hermOff a 0 2 (X 0 2) + hermOff a 1 2 (X 1 2) := by
  have hH : ∀ i j, X j i ^ 2 ^ a = X i j := fun i j => by
    have := congrFun (congrFun hX i) j
    simpa [frobPow] using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOff, unitM, hH]

theorem chi_uMat [Finite F] {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (χ : Matrix (Fin 3) (Fin 3) F → F)
    (hadd : ∀ X Y, IsHerm a X → IsHerm a Y → χ (X + Y) = χ X + χ Y)
    (hsmul : ∀ k : F, k ^ 2 ^ a = k → ∀ X, IsHerm a X → χ (k • X) = k * χ X)
    (hU : ∀ p q r : F, ∀ X, IsHerm a X → χ (twist a (uMat p q r) X) = χ X)
    (h0 : χ (unitM 0) = 0) :
    χ 1 = χ (unitM 2) ∧ (χ (unitM 2) = 0 → ∀ X, IsHerm a X → χ X = 0) := by
  obtain ⟨θ, hθ⟩ := exists_frob_ne ha hF
  have hE : ∀ i : Fin 3, IsHerm a (unitM i : Matrix (Fin 3) (Fin 3) F) := isHerm_unitM a
  have hO : ∀ (i j : Fin 3) (t : F), IsHerm a (hermOff a i j t) := fun i j t =>
    isHerm_hermOff hF i j t
  have hNE : ∀ (i : Fin 3) (t : F), IsHerm a (nrm a t • unitM i : Matrix (Fin 3) (Fin 3) F) :=
    fun i t => isHerm_smul (frob_nrm hF t) (hE i)
  have h11 : χ (unitM 1) = 0 := by
    have h := hU 0 0 1 _ (hO 1 2 θ)
    have hc : (θ * 1 ^ 2 ^ a + θ ^ 2 ^ a * 1 : F) = trc a θ := by rw [one_pow, mul_one, mul_one]
    rw [twist_x12_off12, hc, hadd _ _ (hO 1 2 θ) (isHerm_smul (frob_trc hF θ) (hE 1)),
      hsmul _ (frob_trc hF θ) _ (hE 1)] at h
    have h' : trc a θ * χ (unitM 1) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (trc_ne_zero hθ)
  have hoff : ∀ (i j k : Fin 3) (p q r t : F), χ (unitM k) = 0 → χ (unitM i) = 0 →
      twist a (uMat p q r) (unitM k) = unitM k + nrm a t • unitM i + hermOff a i j t →
      χ (hermOff a i j t) = 0 := by
    intro i j k p q r t hk hi he
    have h := hU p q r _ (hE k)
    rw [he, hadd _ _ (isHerm_add (hE k) (hNE i t)) (hO i j t), hadd _ _ (hE k) (hNE i t),
      hsmul _ (frob_nrm hF t) _ (hE i), hi, mul_zero, add_zero] at h
    linear_combination h
  have h01 : ∀ t, χ (hermOff a 0 1 t) = 0 := fun t => by
    have h := hU t 0 0 _ (hE 1)
    rw [twist_x01_E11, hadd _ _ (isHerm_add (hE 1) (hNE 0 t)) (hO 0 1 t),
      hadd _ _ (hE 1) (hNE 0 t), hsmul _ (frob_nrm hF t) _ (hE 0), h0, mul_zero, add_zero] at h
    linear_combination h
  have h12 : ∀ t, χ (hermOff a 1 2 t) = 0 := fun t => by
    have h := hU 0 0 t _ (hE 2)
    rw [twist_x12_E22, hadd _ _ (isHerm_add (hE 2) (hNE 1 t)) (hO 1 2 t),
      hadd _ _ (hE 2) (hNE 1 t), hsmul _ (frob_nrm hF t) _ (hE 1), h11, mul_zero, add_zero] at h
    linear_combination h
  have h02 : ∀ t, χ (hermOff a 0 2 t) = 0 := fun t => by
    have h := hU 0 t 0 _ (hE 2)
    rw [twist_x02_E22, hadd _ _ (isHerm_add (hE 2) (hNE 0 t)) (hO 0 2 t),
      hadd _ _ (hE 2) (hNE 0 t), hsmul _ (frob_nrm hF t) _ (hE 0), h0, mul_zero, add_zero] at h
    linear_combination h
  have hχX : ∀ X, IsHerm a X → χ X = X 2 2 * χ (unitM 2) := by
    intro X hX
    have hd : ∀ i, IsHerm a (X i i • unitM i : Matrix (Fin 3) (Fin 3) F) := fun i =>
      isHerm_smul (isHerm_diag hX i) (hE i)
    conv_lhs => rw [herm_decomp3 hX]
    rw [hadd _ _ (isHerm_add (isHerm_add (isHerm_add (isHerm_add (hd 0) (hd 1)) (hd 2))
        (hO 0 1 _)) (hO 0 2 _)) (hO 1 2 _),
      hadd _ _ (isHerm_add (isHerm_add (isHerm_add (hd 0) (hd 1)) (hd 2)) (hO 0 1 _)) (hO 0 2 _),
      hadd _ _ (isHerm_add (isHerm_add (hd 0) (hd 1)) (hd 2)) (hO 0 1 _),
      hadd _ _ (isHerm_add (hd 0) (hd 1)) (hd 2), hadd _ _ (hd 0) (hd 1),
      hsmul _ (isHerm_diag hX 0) _ (hE 0), hsmul _ (isHerm_diag hX 1) _ (hE 1),
      hsmul _ (isHerm_diag hX 2) _ (hE 2), h0, h11, h01, h02, h12]
    ring
  refine ⟨?_, fun h2 X hX => by rw [hχX X hX, h2, mul_zero]⟩
  have h1 := hχX 1 (isHerm_one a)
  simp only [Matrix.one_apply_eq, one_mul] at h1
  exact h1

variable (F) in
@[expose] noncomputable def usl3 : Subgroup ↥(StatedSL 3 F) :=
  (Usl F).map (specialLinearGroupEquivStatedSL 3 F).toMonoidHom

omit [CharP F 2] in
theorem uMat_mem_usl3 (p q r : F) : specialLinearGroupEquivStatedSL 3 F (uSL p q r) ∈ usl3 F :=
  Subgroup.mem_map_of_mem _ (uSL_mem_Usl p q r)

omit [CharP F 2] in
theorem coe_uSL_stated (p q r : F) :
    (((specialLinearGroupEquivStatedSL 3 F (uSL p q r) : ↥(StatedSL 3 F)) :
      Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = uMat p q r := rfl

omit [CharP F 2] in
theorem isPGroup_usl3 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) : IsPGroup 2 (usl3 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isPGroup_Usl hF).map _

omit [CharP F 2] in
theorem not_dvd_index_usl3 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    ¬ 2 ∣ (usl3 F).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [usl3, Subgroup.index_map_of_bijective (specialLinearGroupEquivStatedSL 3 F).bijective]
  exact not_dvd_index_Usl hF hn

omit [CharP F 2] in
theorem det_stated3 (γ : ↥(StatedSL 3 F)) :
    ((γ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective γ
  rw [specialLinearGroupEquivStatedSL_coe]
  exact A.2

theorem fix_usl3 [Finite F] {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (X : Matrix (Fin 3) (Fin 3) F) (hX : IsHerm a X)
    (hfix : ∀ u ∈ usl3 F,
      twist a (((u : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) X = X) :
    X = X 0 0 • unitM 0 :=
  fix_uMat ha hF hX (fun t => hfix _ (uMat_mem_usl3 t 0 0)) (hfix _ (uMat_mem_usl3 0 0 1))

theorem chi_usl3 [Finite F] {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (χ : Matrix (Fin 3) (Fin 3) F → F)
    (hadd : ∀ X Y, IsHerm a X → IsHerm a Y → χ (X + Y) = χ X + χ Y)
    (hsmul : ∀ k : F, k ^ 2 ^ a = k → ∀ X, IsHerm a X → χ (k • X) = k * χ X)
    (hU : ∀ u ∈ usl3 F, ∀ X, IsHerm a X →
      χ (twist a (((u : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) X) = χ X)
    (h0 : χ (unitM 0) = 0) :
    χ 1 = χ (unitM 2) ∧ (χ (unitM 2) = 0 → ∀ X, IsHerm a X → χ X = 0) :=
  chi_uMat ha hF χ hadd hsmul (fun p q r X hX => hU _ (uMat_mem_usl3 p q r) X hX) h0

@[expose] def wMat3 : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

omit [CharP F 2] in
theorem wMat3_mul_self : (wMat3 : Matrix (Fin 3) (Fin 3) F) * wMat3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat3, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_wMat3 : (wMat3 : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp [wMat3, Matrix.det_fin_three]
  linear_combination -h2

variable (F) in
@[expose] def wsl3 : ↥(StatedSL 3 F) :=
  ⟨⟨wMat3, wMat3, wMat3_mul_self, wMat3_mul_self⟩, Subgroup.subset_closure det_wMat3⟩

theorem twist_wsl3_E00 (a : ℕ) :
    twist a (((wsl3 F : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) (unitM 0) = unitM 2 := by
  have hp : 2 ^ a ≠ 0 := by positivity
  show twist a wMat3 (unitM 0) = unitM 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fin.sum_univ_three, wMat3, unitM, Matrix.single_apply]

theorem twist_wsl3_one (a : ℕ) :
    twist a (((wsl3 F : ↥(StatedSL 3 F)) : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 1 = 1 := by
  have hp : 2 ^ a ≠ 0 := by positivity
  show twist a wMat3 1 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fin.sum_univ_three, wMat3, Matrix.one_apply]

end SL3

end CFSG.Quasithin.H13.KGLie
