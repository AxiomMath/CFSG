module

public import CFSG.Quasithin.H13.KGLieTwDet
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4Basic

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped Matrix

section Sp4

variable {F : Type} [Field F] [CharP F 2]

abbrev ie0 : Fin 2 ⊕ Fin 2 := Sum.inl 0
abbrev ie1 : Fin 2 ⊕ Fin 2 := Sum.inl 1
abbrev if0 : Fin 2 ⊕ Fin 2 := Sum.inr 0
abbrev if1 : Fin 2 ⊕ Fin 2 := Sum.inr 1

omit [CharP F 2] in
theorem mat_qSp' (x y z : F) :
    (((qSp x y z : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Matrix.fromBlocks 1 !![x, y; y, z] 0 1 := rfl

omit [CharP F 2] in
theorem mat_nSp' (t : F) :
    (((nSp t : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      Matrix.fromBlocks !![1, t; 0, 1] 0 0 (!![1, -t; 0, 1])ᵀ := by
  rw [← mat_apply, nSp, mat_lSp, coe_uGL]
  rfl

omit [CharP F 2] in
theorem qSp_mem_Usp' (x y z : F) : qSp x y z ∈ Usp F := ⟨x, y, z, 0, by rw [nSp_zero, mul_one]⟩

omit [CharP F 2] in
theorem nSp_mem_Usp' (r : F) : nSp r ∈ Usp F := ⟨0, 0, 0, r, by rw [qSp_zero, one_mul]⟩

theorem fix_usp [Finite F] {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (hX : IsHerm a X)
    (hfix : ∀ u ∈ Usp F,
      twist a (((u : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) X = X) :
    X = X ie0 ie0 • unitM ie0 := by
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨θ, hθ⟩ := exists_frob_ne ha hF
  have hp : 2 ^ a ≠ 0 := by positivity
  have hH : ∀ i j, X j i ^ 2 ^ a = X i j := fun i j => by
    have := congrFun (congrFun hX i) j
    simpa [frobPow] using this
  have hq := fun t i j => congrFun (congrFun (hfix _ (qSp_mem_Usp' t 0 0)) i) j
  have hz := fun t i j => congrFun (congrFun (hfix _ (qSp_mem_Usp' 0 0 t)) i) j
  have hn := fun t i j => congrFun (congrFun (hfix _ (nSp_mem_Usp' t)) i) j
  have q01 := hq 1 ie0 ie1
  have q02 := hq 1 ie0 if0
  have q03 := hq 1 ie0 if1
  have q00 := hq 1 ie0 ie0
  have q00' := hq θ ie0 ie0
  have z10 := hz 1 ie1 ie0
  have z12 := hz 1 ie1 if0
  have z13 := hz 1 ie1 if1
  have z11 := hz 1 ie1 ie1
  have z11' := hz θ ie1 ie1
  have n01 := hn 1 ie0 ie1
  have n00 := hn 1 ie0 ie0
  have n00' := hn θ ie0 ie0
  simp only [mat_qSp', mat_nSp'] at q01 q02 q03 q00 q00' z10 z12 z13 z11 z11' n01 n00 n00'
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at q01 q02 q03 q00 q00'
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at z10 z12 z13 z11 z11'
  simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at n01 n00 n00'
  have x_f0e0 : X if0 ie0 = X ie0 if0 := by linear_combination q00 - q02 - X ie0 if0 * h2F
  have y_f0e0 : X if0 ie0 = 0 := by
    have h3 : X if0 ie0 * (θ + θ ^ 2 ^ a) = 0 := by
      linear_combination q00' + θ ^ 2 ^ a * x_f0e0 - (θ * θ ^ 2 ^ a) * q02
    exact (mul_eq_zero.mp h3).resolve_right (trc_ne_zero hθ)
  have y_e0f0 : X ie0 if0 = 0 := by rw [← x_f0e0, y_f0e0]
  have x_f1e1 : X if1 ie1 = X ie1 if1 := by linear_combination z11 - z13 - X ie1 if1 * h2F
  have y_f1e1 : X if1 ie1 = 0 := by
    have h3 : X if1 ie1 * (θ + θ ^ 2 ^ a) = 0 := by
      linear_combination z11' + θ ^ 2 ^ a * x_f1e1 - (θ * θ ^ 2 ^ a) * z13
    exact (mul_eq_zero.mp h3).resolve_right (trc_ne_zero hθ)
  have y_e1f1 : X ie1 if1 = 0 := by rw [← x_f1e1, y_f1e1]
  have x_e1e0 : X ie1 ie0 = X ie0 ie1 := by linear_combination n00 - n01 - X ie0 ie1 * h2F
  have y_e1e0 : X ie1 ie0 = 0 := by
    have h3 : X ie1 ie0 * (θ + θ ^ 2 ^ a) = 0 := by
      linear_combination n00' + θ ^ 2 ^ a * x_e1e0 - (θ * θ ^ 2 ^ a) * n01
    exact (mul_eq_zero.mp h3).resolve_right (trc_ne_zero hθ)
  have y_e0e1 : X ie0 ie1 = 0 := by rw [← x_e1e0, y_e1e0]
  have y_e0f1 : X ie0 if1 = 0 := by rw [← hH ie0 if1, z10, zero_pow hp]
  have y_e1f0 : X ie1 if0 = 0 := by rw [← hH ie1 if0, q01, zero_pow hp]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [unitM, q01, q02, q03, z10, z12, z13, n01, y_f0e0, y_e0f0, y_f1e1,
      y_e1f1, y_e1e0, y_e0e1, y_e0f1, y_e1f0]

abbrev qm (x y z : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks 1 !![x, y; y, z] 0 1

abbrev nm (t : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![1, t; 0, 1] 0 0 (!![1, -t; 0, 1])ᵀ

omit [CharP F 2] in
theorem twist_q_f0 (a : ℕ) (t : F) :
    twist a (qm t 0 0) (unitM if0) = unitM if0 + nrm a t • unitM ie0 + hermOff a ie0 if0 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, unitM, hermOff,
      Matrix.single_apply, nrm]

omit [CharP F 2] in
theorem twist_z_f1 (a : ℕ) (t : F) :
    twist a (qm 0 0 t) (unitM if1) = unitM if1 + nrm a t • unitM ie1 + hermOff a ie1 if1 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, unitM, hermOff,
      Matrix.single_apply, nrm]

omit [CharP F 2] in
theorem twist_z_off (a : ℕ) (s t : F) :
    twist a (qm 0 0 t) (hermOff a ie1 if1 s) =
      hermOff a ie1 if1 s + (s * t ^ 2 ^ a + s ^ 2 ^ a * t) • unitM ie1 := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, unitM, hermOff,
      Matrix.single_apply]
  all_goals ring

omit [CharP F 2] in
theorem twist_n_e1 (a : ℕ) (t : F) :
    twist a (nm t) (unitM ie1) = unitM ie1 + nrm a t • unitM ie0 + hermOff a ie0 ie1 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, unitM, hermOff,
      Matrix.single_apply, nrm]

theorem twist_n_f0 (a : ℕ) (t : F) :
    twist a (nm t) (unitM if0) = unitM if0 + nrm a t • unitM if1 + hermOff a if1 if0 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, unitM, hermOff,
      Matrix.single_apply, nrm, CharTwo.neg_eq]

theorem twist_n_off (a : ℕ) (s t : F) :
    twist a (nm t) (hermOff a if1 if0 s) =
      hermOff a if1 if0 s + (s * t ^ 2 ^ a + s ^ 2 ^ a * t) • unitM if1 := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, unitM, hermOff,
      Matrix.single_apply, CharTwo.neg_eq]
  all_goals ring

omit [CharP F 2] in
theorem twist_y_f0 (a : ℕ) (t : F) :
    twist a (qm 0 t 0) (unitM if0) = unitM if0 + nrm a t • unitM ie1 + hermOff a ie1 if0 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, unitM, hermOff,
      Matrix.single_apply, nrm]

omit [CharP F 2] in
theorem twist_y_f1 (a : ℕ) (t : F) :
    twist a (qm 0 t 0) (unitM if1) = unitM if1 + nrm a t • unitM ie0 + hermOff a ie0 if1 t := by
  have hp : 2 ^ a ≠ 0 := by positivity
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, unitM, hermOff,
      Matrix.single_apply, nrm]

omit [CharP F 2] in
theorem herm_decomp4 {a : ℕ} {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hX : IsHerm a X) :
    X = X ie0 ie0 • unitM ie0 + X ie1 ie1 • unitM ie1 + X if0 if0 • unitM if0 +
      X if1 if1 • unitM if1 + hermOff a ie0 ie1 (X ie0 ie1) + hermOff a ie0 if0 (X ie0 if0) +
      hermOff a ie0 if1 (X ie0 if1) + hermOff a ie1 if0 (X ie1 if0) +
      hermOff a ie1 if1 (X ie1 if1) + hermOff a if1 if0 (X if1 if0) := by
  have hH : ∀ i j, X j i ^ 2 ^ a = X i j := fun i j => by
    have := congrFun (congrFun hX i) j
    simpa [frobPow] using this
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [hermOff, unitM, hH]

theorem chi_usp [Finite F] {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (χ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F → F)
    (hadd : ∀ X Y, IsHerm a X → IsHerm a Y → χ (X + Y) = χ X + χ Y)
    (hsmul : ∀ k : F, k ^ 2 ^ a = k → ∀ X, IsHerm a X → χ (k • X) = k * χ X)
    (hU : ∀ u ∈ Usp F, ∀ X, IsHerm a X →
      χ (twist a (((u : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) X) = χ X)
    (h0 : χ (unitM ie0) = 0) :
    χ 1 = χ (unitM if0) ∧ (χ (unitM if0) = 0 → ∀ X, IsHerm a X → χ X = 0) := by
  obtain ⟨θ, hθ⟩ := exists_frob_ne ha hF
  have hE : ∀ i, IsHerm a (unitM i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := isHerm_unitM a
  have hO : ∀ (i j : Fin 2 ⊕ Fin 2) (t : F), IsHerm a (hermOff a i j t) := fun i j t =>
    isHerm_hermOff hF i j t
  have hNE : ∀ (i : Fin 2 ⊕ Fin 2) (t : F),
      IsHerm a (nrm a t • unitM i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :=
    fun i t => isHerm_smul (frob_nrm hF t) (hE i)
  have hq : ∀ x y z X, IsHerm a X → χ (twist a (qm x y z) X) = χ X := fun x y z X hX => by
    have := hU _ (qSp_mem_Usp' x y z) X hX
    rwa [mat_qSp'] at this
  have hn : ∀ t X, IsHerm a X → χ (twist a (nm t) X) = χ X := fun t X hX => by
    have := hU _ (nSp_mem_Usp' t) X hX
    rwa [mat_nSp'] at this
  have hc : (θ * 1 ^ 2 ^ a + θ ^ 2 ^ a * 1 : F) = trc a θ := by rw [one_pow, mul_one, mul_one]
  have h11 : χ (unitM ie1) = 0 := by
    have h := hq 0 0 1 _ (hO ie1 if1 θ)
    rw [twist_z_off, hc, hadd _ _ (hO ie1 if1 θ) (isHerm_smul (frob_trc hF θ) (hE ie1)),
      hsmul _ (frob_trc hF θ) _ (hE ie1)] at h
    have h' : trc a θ * χ (unitM ie1) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (trc_ne_zero hθ)
  have h33 : χ (unitM if1) = 0 := by
    have h := hn 1 _ (hO if1 if0 θ)
    rw [twist_n_off, hc, hadd _ _ (hO if1 if0 θ) (isHerm_smul (frob_trc hF θ) (hE if1)),
      hsmul _ (frob_trc hF θ) _ (hE if1)] at h
    have h' : trc a θ * χ (unitM if1) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (trc_ne_zero hθ)
  have hoff : ∀ (k i j : Fin 2 ⊕ Fin 2) (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (t : F),
      χ (twist a g (unitM k)) = χ (unitM k) → χ (unitM i) = 0 →
      twist a g (unitM k) = unitM k + nrm a t • unitM i + hermOff a i j t →
      χ (hermOff a i j t) = 0 := by
    intro k i j g t hk hi he
    rw [he, hadd _ _ (isHerm_add (hE k) (hNE i t)) (hO i j t), hadd _ _ (hE k) (hNE i t),
      hsmul _ (frob_nrm hF t) _ (hE i), hi, mul_zero, add_zero] at hk
    linear_combination hk
  have h01 : ∀ t, χ (hermOff a ie0 ie1 t) = 0 := fun t =>
    hoff ie1 ie0 ie1 _ t (hn t _ (hE ie1)) h0 (twist_n_e1 a t)
  have h02 : ∀ t, χ (hermOff a ie0 if0 t) = 0 := fun t =>
    hoff if0 ie0 if0 _ t (hq t 0 0 _ (hE if0)) h0 (twist_q_f0 a t)
  have h03 : ∀ t, χ (hermOff a ie0 if1 t) = 0 := fun t =>
    hoff if1 ie0 if1 _ t (hq 0 t 0 _ (hE if1)) h0 (twist_y_f1 a t)
  have h12 : ∀ t, χ (hermOff a ie1 if0 t) = 0 := fun t =>
    hoff if0 ie1 if0 _ t (hq 0 t 0 _ (hE if0)) h11 (twist_y_f0 a t)
  have h13 : ∀ t, χ (hermOff a ie1 if1 t) = 0 := fun t =>
    hoff if1 ie1 if1 _ t (hq 0 0 t _ (hE if1)) h11 (twist_z_f1 a t)
  have h32 : ∀ t, χ (hermOff a if1 if0 t) = 0 := fun t =>
    hoff if0 if1 if0 _ t (hn t _ (hE if0)) h33 (twist_n_f0 a t)
  have hχX : ∀ X, IsHerm a X → χ X = X if0 if0 * χ (unitM if0) := by
    intro X hX
    have hd : ∀ i, IsHerm a (X i i • unitM i : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :=
      fun i => isHerm_smul (isHerm_diag hX i) (hE i)
    conv_lhs => rw [herm_decomp4 hX]
    have s1 := isHerm_add (hd ie0) (hd ie1)
    have s2 := isHerm_add s1 (hd if0)
    have s3 := isHerm_add s2 (hd if1)
    have s4 := isHerm_add s3 (hO ie0 ie1 (X ie0 ie1))
    have s5 := isHerm_add s4 (hO ie0 if0 (X ie0 if0))
    have s6 := isHerm_add s5 (hO ie0 if1 (X ie0 if1))
    have s7 := isHerm_add s6 (hO ie1 if0 (X ie1 if0))
    have s8 := isHerm_add s7 (hO ie1 if1 (X ie1 if1))
    rw [hadd _ _ s8 (hO _ _ _), hadd _ _ s7 (hO _ _ _), hadd _ _ s6 (hO _ _ _),
      hadd _ _ s5 (hO _ _ _), hadd _ _ s4 (hO _ _ _), hadd _ _ s3 (hO _ _ _),
      hadd _ _ s2 (hd if1), hadd _ _ s1 (hd if0), hadd _ _ (hd ie0) (hd ie1),
      hsmul _ (isHerm_diag hX ie0) _ (hE ie0), hsmul _ (isHerm_diag hX ie1) _ (hE ie1),
      hsmul _ (isHerm_diag hX if0) _ (hE if0), hsmul _ (isHerm_diag hX if1) _ (hE if1), h0, h11,
      h33, h01, h02, h03, h12, h13, h32]
    ring
  refine ⟨?_, fun h2 X hX => by rw [hχX X hX, h2, mul_zero]⟩
  have h1 := hχX 1 (isHerm_one a)
  simp only [Matrix.one_apply_eq, one_mul] at h1
  exact h1

@[expose] def wMat4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.of fun i j => if Equiv.swap ie0 if0 j = i then 1 else 0

omit [CharP F 2] in
theorem wMat4_mul_self : (wMat4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * wMat4 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [wMat4, Matrix.mul_apply, Equiv.swap_apply_def]

theorem wMat4_symp : (wMat4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2 * wMat4 =
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [wMat4, Matrix.mul_apply, Equiv.swap_apply_def,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, CharTwo.neg_eq]

variable (F) in
@[expose] def wsp : ↥(StatedSp 2 F) :=
  ⟨⟨wMat4, wMat4, wMat4_mul_self, wMat4_mul_self⟩,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.mem_statedSp_iff.2 wMat4_symp⟩

theorem twist_wsp_e0 (a : ℕ) :
    twist a (((wsp F : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (unitM ie0) = unitM if0 := by
  have hp : 2 ^ a ≠ 0 := by positivity
  show twist a wMat4 (unitM ie0) = unitM if0
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, wMat4, Equiv.swap_apply_def,
      unitM, Matrix.single_apply]

theorem twist_wsp_one (a : ℕ) :
    twist a (((wsp F : ↥(StatedSp 2 F)) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) 1 = 1 := by
  have hp : 2 ^ a ≠ 0 := by positivity
  show twist a wMat4 1 = 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [twist_apply, Fintype.sum_sum_type, Fin.sum_univ_two, wMat4, Equiv.swap_apply_def,
      Matrix.one_apply]

theorem det_statedSp (γ : ↥(StatedSp 2 F)) :
    ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det = 1 := by
  have h := CFSG.ClassicalInvolution.Models.SymplecticPairs.mem_statedSp_iff.1 γ.2
  have hJ : (CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2).det ≠ 0 := by
    have hJ2 : CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2 *
        CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2 = 1 := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fintype.sum_sum_type,
          CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, CharTwo.neg_eq, Matrix.one_apply]
    intro h0
    have := congrArg Matrix.det hJ2
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  set d := ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det
  have h3 : (d * d - 1) * (CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F 2).det = 0 := by
    linear_combination h2
  have h4 : d * d = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hJ)
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have h5 : (d - 1) ^ 2 = 0 := by linear_combination h4 - d * h2F + h2F
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h5)

end Sp4

end CFSG.Quasithin.H13.KGLie
