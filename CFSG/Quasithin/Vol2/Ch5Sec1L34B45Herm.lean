module

public import CFSG.Quasithin.Background.HL3NineModel
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact2

public section

namespace CFSG.Quasithin.H13.B45L34

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

@[expose] def rad2 (b c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, c; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_rad2 (b c : F) :
    ((rad2 b c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, c; 0, 1, b; 0, 0, 1] := rfl

variable [CharP F 2] [Finite F]

theorem tw_rad (b c : F) (X : Matrix (Fin 3) (Fin 3) F) :
    tw 1 ((KGL34P.rad b c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) X =
      !![X 0 0 + b * X 1 0 + c * X 2 0 + b ^ 2 * (X 0 1 + b * X 1 1 + c * X 2 1) +
          c ^ 2 * (X 0 2 + b * X 1 2 + c * X 2 2),
        X 0 1 + b * X 1 1 + c * X 2 1, X 0 2 + b * X 1 2 + c * X 2 2;
        X 1 0 + b ^ 2 * X 1 1 + c ^ 2 * X 1 2, X 1 1, X 1 2;
        X 2 0 + b ^ 2 * X 2 1 + c ^ 2 * X 2 2, X 2 1, X 2 2] := by
  rw [tw, conjM_eq_map_pow, KGL34P.coe_rad]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.vecMul,
      dotProduct] <;> ring

theorem tw_rad2 (b c : F) (X : Matrix (Fin 3) (Fin 3) F) :
    tw 1 ((rad2 b c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) X =
      !![X 0 0 + c * X 2 0 + c ^ 2 * (X 0 2 + c * X 2 2), X 0 1 + c * X 2 1 +
          b ^ 2 * (X 0 2 + c * X 2 2), X 0 2 + c * X 2 2;
        X 1 0 + b * X 2 0 + c ^ 2 * (X 1 2 + b * X 2 2), X 1 1 + b * X 2 1 +
          b ^ 2 * (X 1 2 + b * X 2 2), X 1 2 + b * X 2 2;
        X 2 0 + c ^ 2 * X 2 2, X 2 1 + b ^ 2 * X 2 2, X 2 2] := by
  rw [tw, conjM_eq_map_pow, coe_rad2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.vecMul,
      dotProduct] <;> ring

variable (hK : Nat.card F = (2 ^ 1) ^ 2)
include hK

theorem mat_eq_zero_of_fix_rad {X : HMod 1 F} (hX : ∀ b c : F, rho hK (KGL34P.rad b c) X = X)
    (i j : Fin 3) (hij : ¬ (i = 0 ∧ j = 0)) : mat X i j = 0 := by
  have hk : Nat.card F = 4 := by rw [hK]; norm_num
  obtain ⟨ω, -, hω2⟩ := KGL34P.exists_primitive_cube_root hk
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have key : ∀ b c : F,
      tw 1 ((KGL34P.rad b c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        (mat X) = mat X := by
    intro b c
    have := congrArg mat (hX b c)
    rwa [mat_rho] at this
  have e1 := key 1 0
  have e2 := key 0 1
  have e3 := key ω 0
  have e4 := key 0 ω
  rw [tw_rad (F := F)] at e1 e2 e3 e4
  have a10 := Matrix.ext_iff.mpr e1 1 0
  have a20 := Matrix.ext_iff.mpr e1 2 0
  have a00 := Matrix.ext_iff.mpr e1 0 0
  have b10 := Matrix.ext_iff.mpr e2 1 0
  have b20 := Matrix.ext_iff.mpr e2 2 0
  have b00 := Matrix.ext_iff.mpr e2 0 0
  have c00 := Matrix.ext_iff.mpr e3 0 0
  have d00 := Matrix.ext_iff.mpr e4 0 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.tail_cons,
    Matrix.head_fin_const] at a10 a20 a00 b10 b20 b00 c00 d00
  have x11 : mat X 1 1 = 0 := by linear_combination a10
  have x21 : mat X 2 1 = 0 := by linear_combination a20
  have x12 : mat X 1 2 = 0 := by linear_combination b10
  have x22 : mat X 2 2 = 0 := by linear_combination b20
  have y1 : mat X 1 0 + mat X 0 1 = 0 := by linear_combination a00 - x11
  have y2 : ω * mat X 1 0 + ω ^ 2 * mat X 0 1 = 0 := by
    linear_combination c00 - ω ^ 3 * x11
  have z1 : mat X 2 0 + mat X 0 2 = 0 := by linear_combination b00 - x22
  have z2 : ω * mat X 2 0 + ω ^ 2 * mat X 0 2 = 0 := by linear_combination d00 - ω ^ 3 * x22
  have x10 : mat X 1 0 = 0 := by
    linear_combination ω ^ 2 * y1 - y2 + mat X 1 0 * hω2 - ω ^ 2 * mat X 1 0 * h2
  have x01 : mat X 0 1 = 0 := by linear_combination y1 - x10
  have x20 : mat X 2 0 = 0 := by
    linear_combination ω ^ 2 * z1 - z2 + mat X 2 0 * hω2 - ω ^ 2 * mat X 2 0 * h2
  have x02 : mat X 0 2 = 0 := by linear_combination z1 - x20
  fin_cases i <;> fin_cases j
  · exact absurd ⟨rfl, rfl⟩ hij
  all_goals assumption

theorem card_fix_rad_le :
    Nat.card {X : HMod 1 F // ∀ b c : F, rho hK (KGL34P.rad b c) X = X} ≤ 2 := by
  classical
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let φ : {X : HMod 1 F // ∀ b c : F, rho hK (KGL34P.rad b c) X = X} → Bool :=
    fun X => decide (mat X.1 0 0 = 0)
  have h00 : ∀ X : HMod 1 F, mat X 0 0 = 0 ∨ mat X 0 0 = 1 := by
    intro X
    have hb := herm_apply X 0 0
    rw [bar_apply, pow_one] at hb
    have : mat X 0 0 * (mat X 0 0 - 1) = 0 := by linear_combination hb
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hinj : Function.Injective φ := by
    intro X Y hXY
    apply Subtype.ext
    apply mat_injective
    ext i j
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [φ, decide_eq_decide] at hXY
      rcases h00 X.1 with hx | hx <;> rcases h00 Y.1 with hy | hy
      · rw [hx, hy]
      · exact absurd (hXY.mp hx) (by rw [hy]; exact one_ne_zero)
      · exact absurd (hXY.mpr hy) (by rw [hx]; exact one_ne_zero)
      · rw [hx, hy]
    · rw [mat_eq_zero_of_fix_rad hK X.2 i j hij, mat_eq_zero_of_fix_rad hK Y.2 i j hij]
  have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  exact (Nat.card_le_card_of_injective φ hinj).trans_eq hb

@[expose] noncomputable def diag01 (p q : Bool) : HMod 1 F :=
  mkH !![(if p then 1 else 0 : F), 0, 0; 0, (if q then 1 else 0 : F), 0; 0, 0, 0] (by
    rw [conjM_eq_map_pow]
    ext i j
    fin_cases i <;> fin_cases j <;> cases p <;> cases q <;> simp)

omit hK in
theorem mat_diag01 (p q : Bool) :
    mat (diag01 (F := F) p q) =
      !![(if p then 1 else 0 : F), 0, 0; 0, (if q then 1 else 0 : F), 0; 0, 0, 0] := rfl

theorem four_le_card_fix_rad2 :
    4 ≤ Nat.card {X : HMod 1 F // ∀ b c : F, rho hK (rad2 b c) X = X} := by
  classical
  have hfix : ∀ p q : Bool, ∀ b c : F, rho hK (rad2 b c) (diag01 p q) = diag01 p q := by
    intro p q b c
    apply mat_injective
    rw [mat_rho, mat_diag01, tw_rad2 (F := F)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  let φ : Bool × Bool → {X : HMod 1 F // ∀ b c : F, rho hK (rad2 b c) X = X} :=
    fun pq => ⟨diag01 pq.1 pq.2, hfix pq.1 pq.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    have h' := congrArg (fun X => mat X.1) h
    simp only [φ, mat_diag01] at h'
    have e00 := Matrix.ext_iff.mpr h' 0 0
    have e11 := Matrix.ext_iff.mpr h' 1 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e11
    cases p <;> cases q <;> cases p' <;> cases q' <;> simp_all
  have hb : Nat.card (Bool × Bool) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool]
  exact hb.symm.le.trans (Nat.card_le_card_of_injective φ hinj)

theorem rho_eq_one_of_mem_scalars {z : SpecialLinearGroup (Fin 3) F} (hz : z ∈ scalars 3 F) :
    rho hK z = 1 := by
  obtain ⟨c, hc, hzc⟩ := mem_scalars.mp hz
  refine MulEquiv.ext fun X => mat_injective ?_
  rw [mat_rho, hzc]
  show tw 1 (scalar (Fin 3) (c : F)) (mat X) = mat X
  have hc3 : (c : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  rw [tw, conjM_eq_map_pow, scalar_apply, Matrix.diagonal_map (by simp),
    Matrix.diagonal_transpose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  linear_combination mat X i j * hc3

@[expose] noncomputable def rhoP : projectiveSL 3 F →* MulAut (HMod 1 F) :=
  QuotientGroup.lift (scalars 3 F) (rho hK) fun _ hz =>
    (MonoidHom.mem_ker).mpr (rho_eq_one_of_mem_scalars hK hz)

theorem rhoP_proj (g : SpecialLinearGroup (Fin 3) F) : rhoP hK (proj 3 F g) = rho hK g := rfl

end CFSG.Quasithin.H13.B45L34
