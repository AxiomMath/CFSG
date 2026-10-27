module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinCentralizerLam
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix
open CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.ClassicalInvolution.Models.SymplecticPairs

variable {F : Type} [Field F]

private theorem eq_zero_of_nilpotent_of_diagonal [CharP F 2] {N : Matrix (Fin 2) (Fin 2) F}
    (h01 : N 0 1 = 0) (h10 : N 1 0 = 0) (hd : N 1 1 = N 0 0) {e : ℕ}
    (he : N ^ 2 ^ e = 0) : N = 0 := by
  have hN_form : N = !![N 0 0, 0; 0, N 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val', hd, h01, h10]
  have hN_diag : N = Matrix.diagonal ![N 0 0, N 0 0] := by
    rw [hN_form]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val', Matrix.diagonal]
  have h := he
  rw [hN_diag] at h
  rw [Matrix.diagonal_pow] at h
  have h00' : (N 0 0) ^ 2 ^ e = 0 := by
    have := congrFun (congrFun h 0) 0
    simpa [Matrix.diagonal, Matrix.cons_val, Matrix.cons_val'] using this
  have h00 : N 0 0 = 0 := IsNilpotent.eq_zero ⟨2 ^ e, h00'⟩
  rw [hN_form, h00]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val', Matrix.zero_apply]

theorem eq_one_of_commute_of_trace_ne_zero_of_pow_two_pow [CharP F 2]
    {g h : Matrix (Fin 2) (Fin 2) F} (htr : g.trace ≠ 0)
    (hgh : h * g = g * h) {e : ℕ} (he : h ^ 2 ^ e = 1) : h = 1 := by
  let N : Matrix (Fin 2) (Fin 2) F := h + 1
  have hN : N ^ 2 ^ e = 0 := by
    dsimp only [N]
    rw [add_pow_char_pow_of_commute 2 e (Commute.one_right h), he, one_pow]
    exact CharTwo.add_self_eq_zero 1
  have htrN : N.trace = 0 := (Matrix.isNilpotent_trace_of_isNilpotent ⟨2 ^ e, hN⟩).eq_zero
  have hd : N 1 1 = N 0 0 := by
    have h : N 0 0 + N 1 1 = 0 := by simpa [Matrix.trace_fin_two] using htrN
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  have hNg : N * g = g * N := by
    dsimp only [N]
    calc (h + 1) * g = h * g + g := by rw [add_mul, one_mul]
      _ = g * h + g := by rw [hgh]
      _ = g * (h + 1) := by rw [mul_add, mul_one]
  have htr' : g 1 1 + g 0 0 ≠ 0 := by
    rw [add_comm, ← Matrix.trace_fin_two]
    exact htr
  have htr'' : g 0 0 + g 1 1 ≠ 0 := by
    rw [← Matrix.trace_fin_two]
    exact htr
  have h01 : N 0 1 = 0 := by
    have e12 : N 0 0 * g 0 1 + N 0 1 * g 1 1 = g 0 0 * N 0 1 + g 0 1 * N 1 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hNg 0) 1
    rw [hd, mul_comm (N 0 0) (g 0 1), add_comm (g 0 0 * N 0 1) (g 0 1 * N 0 0)] at e12
    have h12 : N 0 1 * g 1 1 = g 0 0 * N 0 1 := add_left_cancel e12
    have hzero : N 0 1 * (g 1 1 + g 0 0) = 0 := by
      rw [mul_add, h12, mul_comm (g 0 0) (N 0 1), CharTwo.add_self_eq_zero]
    exact (mul_eq_zero.mp hzero).resolve_right htr'
  have h10 : N 1 0 = 0 := by
    have e21 : N 1 0 * g 0 0 + N 1 1 * g 1 0 = g 1 0 * N 0 0 + g 1 1 * N 1 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hNg 1) 0
    rw [hd, mul_comm (N 0 0) (g 1 0), add_comm (N 1 0 * g 0 0) (g 1 0 * N 0 0)] at e21
    have h21 : N 1 0 * g 0 0 = g 1 1 * N 1 0 := add_left_cancel e21
    have hzero : N 1 0 * (g 0 0 + g 1 1) = 0 := by
      rw [mul_add, h21, mul_comm (g 1 1) (N 1 0), CharTwo.add_self_eq_zero]
    exact (mul_eq_zero.mp hzero).resolve_right htr''
  have hN_zero : N = 0 := eq_zero_of_nilpotent_of_diagonal h01 h10 hd hN
  dsimp only [N] at hN_zero
  have h_eq : h = 1 := by
    calc h = h + 0 := by rw [add_zero]
      _ = h + (1 + 1) := by rw [CharTwo.add_self_eq_zero 1]
      _ = h + 1 + 1 := by rw [add_assoc]
      _ = 0 + 1 := by rw [hN_zero]
      _ = 1 := by rw [zero_add]
  exact h_eq

theorem det_sub_one_eq_trace_of_det_eq_one [CharP F 2] (M : Matrix (Fin 2) (Fin 2) F)
    (hM : M.det = 1) : (M - 1).det = M.trace := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), CharTwo.sub_eq_add]
  have hM' : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hM
    rw [CharTwo.sub_eq_add] at hM
    exact hM
  have h3 : M 0 0 * M 1 1 + M 0 1 * M 1 0 + 1 = 0 := by
    rw [hM']
    exact CharTwo.add_self_eq_zero 1
  linear_combination h3

private theorem vecMul_pairMat_apply_inl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (v : ι → R) :
    (v ᵥ* pairMat a b g) a = v a * g 0 0 + v b * g 1 0 := by
  rw [Matrix.vecMul_apply_eq_sum,
    Fintype.sum_eq_add a b hab (fun x hx => by
      rw [pairMat_apply_of_ne hx.1 hx.2, one_apply_ne hx.1, mul_zero])]
  obtain ⟨h1, _, h3, _⟩ := pairMat_apply_pair hab g
  rw [h1, h3]

private theorem vecMul_pairMat_apply_inr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (v : ι → R) :
    (v ᵥ* pairMat a b g) b = v a * g 0 1 + v b * g 1 1 := by
  rw [Matrix.vecMul_apply_eq_sum,
    Fintype.sum_eq_add a b hab (fun x hx => by
      rw [pairMat_apply_of_ne hx.1 hx.2, one_apply_ne hx.2, mul_zero])]
  obtain ⟨_, h2, _, h4⟩ := pairMat_apply_pair hab g
  rw [h2, h4]

private theorem vecMul_pairMat_row_inl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) :
    (pairMat a b g a) ᵥ* M = g 0 0 • (M a) + g 0 1 • (M b) := by
  ext c
  rw [Matrix.vecMul_apply_eq_sum]
  rw [Fintype.sum_eq_add a b hab (fun x hx => by
    rw [pairMat_apply_fst_of_ne hx.1 hx.2, zero_mul])]
  obtain ⟨h1, h2, _, _⟩ := pairMat_apply_pair hab g
  rw [h1, h2]
  simp

private theorem vecMul_pairMat_row_inr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) :
    (pairMat a b g b) ᵥ* M = g 1 0 • (M a) + g 1 1 • (M b) := by
  ext c
  rw [Matrix.vecMul_apply_eq_sum]
  rw [Fintype.sum_eq_add a b hab (fun x hx => by
    rw [pairMat_apply_snd_of_ne hab hx.1 hx.2, zero_mul])]
  obtain ⟨_, _, h3, h4⟩ := pairMat_apply_pair hab g
  rw [h3, h4]
  simp

theorem eq_zero_pair_of_fixed_left_of_trace_ne_zero [CharP F 2]
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {x₀ x₁ : F}
    (h₀ : x₀ * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + x₁ * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = x₀)
    (h₁ : x₀ * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + x₁ * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = x₁) :
    x₀ = 0 ∧ x₁ = 0 := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) F) - 1).det ≠ 0 := by
    rw [det_sub_one_eq_trace_of_det_eq_one _ (Matrix.SpecialLinearGroup.det_coe g)]
    exact htr
  have hx : (![x₀, x₁] : Fin 2 → F) ᵥ* ((g : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
    rw [funext_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Pi.zero_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
      rw [CharTwo.sub_eq_add, mul_add, mul_one, add_right_comm, h₀]
      exact CharTwo.add_self_eq_zero _
    · rw [Pi.zero_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), sub_zero]
      rw [CharTwo.sub_eq_add, mul_add, mul_one, ← add_assoc, h₁]
      exact CharTwo.add_self_eq_zero _
  have hzero := Matrix.eq_zero_of_vecMul_eq_zero hdet hx
  exact ⟨by simpa using congrFun hzero 0, by simpa using congrFun hzero 1⟩

private theorem row_zero_of_commute_lam [CharP F 2] {m : ℕ} {j : Fin m}
    {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {u : StatedSp m F}
    (hu : u * lam j g = lam j g * u) :
    ∀ r : Fin m ⊕ Fin m, r ≠ Sum.inl j → r ≠ Sum.inr j →
      mat m F u r (Sum.inl j) = 0 ∧ mat m F u r (Sum.inr j) = 0 := by
  have hcommM : mat m F u * mat m F (lam j g) = mat m F (lam j g) * mat m F u := by
    have h := congrArg (mat m F) hu
    rw [map_mul, map_mul] at h
    exact h
  have hzero_plane : Sum.inl j ≠ (Sum.inr j : Fin m ⊕ Fin m) := Sum.inl_ne_inr
  intro r hra hrb
  have hrow : mat m F u r ᵥ* mat m F (lam j g) = mat m F u r := by
    have h1 : mat m F u r ᵥ* mat m F (lam j g) =
        (mat m F u * mat m F (lam j g)) r :=
      (Matrix.mul_apply_eq_vecMul _ _ r).symm
    have h3 : (mat m F (lam j g) * mat m F u) r = mat m F u r := by
      rw [Matrix.mul_apply_eq_vecMul]
      have hΓr : mat m F (lam j g) r = (1 : Matrix (Fin m ⊕ Fin m)
          (Fin m ⊕ Fin m) F) r := by
        funext x
        rw [mat_lam]
        exact pairMat_apply_of_ne hra hrb (g : Matrix (Fin 2) (Fin 2) F) x
      rw [hΓr, ← Matrix.mul_apply_eq_vecMul, Matrix.one_mul]
    rw [h1, hcommM, h3]
  refine eq_zero_pair_of_fixed_left_of_trace_ne_zero htr ?_ ?_
  · have h := congrFun hrow (Sum.inl j)
    rw [mat_lam, vecMul_pairMat_apply_inl hzero_plane] at h
    exact h
  · have h := congrFun hrow (Sum.inr j)
    rw [mat_lam, vecMul_pairMat_apply_inr hzero_plane] at h
    exact h

private theorem block_commutes_of_commute_lam [CharP F 2] {m : ℕ} {j : Fin m}
    {g : SpecialLinearGroup (Fin 2) F} {u : StatedSp m F}
    (hu : u * lam j g = lam j g * u) :
    let h : Matrix (Fin 2) (Fin 2) F := !![mat m F u (Sum.inl j) (Sum.inl j),
        mat m F u (Sum.inl j) (Sum.inr j); mat m F u (Sum.inr j) (Sum.inl j),
        mat m F u (Sum.inr j) (Sum.inr j)]
    h * (g : Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F) * h := by
  have hcommM : mat m F u * mat m F (lam j g) = mat m F (lam j g) * mat m F u := by
    have h := congrArg (mat m F) hu
    rw [map_mul, map_mul] at h
    exact h
  let M := mat m F u
  let Γ := mat m F (lam j g)
  have hΓ : Γ = pairMat (Sum.inl j) (Sum.inr j) ((g : Matrix (Fin 2) (Fin 2) F)) := mat_lam j g
  have hzero_plane : Sum.inl j ≠ (Sum.inr j : Fin m ⊕ Fin m) := Sum.inl_ne_inr
  have hrow1 : M (Sum.inl j) ᵥ* Γ = Γ (Sum.inl j) ᵥ* M := by
    have h := congrFun hcommM (Sum.inl j)
    rwa [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul] at h
  have hrow2 : M (Sum.inr j) ᵥ* Γ = Γ (Sum.inr j) ᵥ* M := by
    have h := congrFun hcommM (Sum.inr j)
    rwa [Matrix.mul_apply_eq_vecMul, Matrix.mul_apply_eq_vecMul] at h
  ext i k
  fin_cases i <;> fin_cases k <;> simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · have h := congrFun hrow1 (Sum.inl j)
    rw [hΓ, vecMul_pairMat_apply_inl hzero_plane, vecMul_pairMat_row_inl hzero_plane] at h
    simp [M, h]
  · have h := congrFun hrow1 (Sum.inr j)
    rw [hΓ, vecMul_pairMat_apply_inr hzero_plane, vecMul_pairMat_row_inl hzero_plane] at h
    simp [M, h]
  · have h := congrFun hrow2 (Sum.inl j)
    rw [hΓ, vecMul_pairMat_apply_inl hzero_plane, vecMul_pairMat_row_inr hzero_plane] at h
    simp [M, h]
  · have h := congrFun hrow2 (Sum.inr j)
    rw [hΓ, vecMul_pairMat_apply_inr hzero_plane, vecMul_pairMat_row_inr hzero_plane] at h
    simp [M, h]

private theorem block_action_of_commute_lam [CharP F 2] {m : ℕ} {j : Fin m}
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {u : StatedSp m F} (hu : u * lam j g = lam j g * u) :
    let M := mat m F u
    let h : Matrix (Fin 2) (Fin 2) F := !![M (Sum.inl j) (Sum.inl j),
        M (Sum.inl j) (Sum.inr j); M (Sum.inr j) (Sum.inl j), M (Sum.inr j) (Sum.inr j)]
    M *ᵥ Pi.single (Sum.inl j) 1 =
        h 0 0 • Pi.single (Sum.inl j) 1 + h 1 0 • Pi.single (Sum.inr j) 1 ∧
    M *ᵥ Pi.single (Sum.inr j) 1 =
        h 0 1 • Pi.single (Sum.inl j) 1 + h 1 1 • Pi.single (Sum.inr j) 1 := by
  let M := mat m F u
  let h : Matrix (Fin 2) (Fin 2) F := !![M (Sum.inl j) (Sum.inl j),
      M (Sum.inl j) (Sum.inr j); M (Sum.inr j) (Sum.inl j), M (Sum.inr j) (Sum.inr j)]
  let e1 : Fin m ⊕ Fin m → F := Pi.single (Sum.inl j) 1
  let e2 : Fin m ⊕ Fin m → F := Pi.single (Sum.inr j) 1
  have hrow_zero := row_zero_of_commute_lam htr hu
  constructor
  · funext r
    by_cases hr1 : r = Sum.inl j
    · subst hr1
      rw [mulVec_single_one_apply]
      simp
    by_cases hr2 : r = Sum.inr j
    · subst hr2
      rw [mulVec_single_one_apply]
      simp
    · rw [mulVec_single_one_apply, (hrow_zero r hr1 hr2).1]
      simp [Pi.single, hr1, hr2]
  · funext r
    by_cases hr1 : r = Sum.inl j
    · subst hr1
      rw [mulVec_single_one_apply]
      simp
    by_cases hr2 : r = Sum.inr j
    · subst hr2
      rw [mulVec_single_one_apply]
      simp
    · rw [mulVec_single_one_apply, (hrow_zero r hr1 hr2).2]
      simp [Pi.single, hr1, hr2]

private theorem block_pow_eq_of_commute_lam [CharP F 2] {m : ℕ} {j : Fin m}
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {u : StatedSp m F} (hu : u * lam j g = lam j g * u) :
    let M := mat m F u
    let h : Matrix (Fin 2) (Fin 2) F := !![M (Sum.inl j) (Sum.inl j),
        M (Sum.inl j) (Sum.inr j); M (Sum.inr j) (Sum.inl j), M (Sum.inr j) (Sum.inr j)]
    ∀ k : ℕ, M ^ k *ᵥ Pi.single (Sum.inl j) 1 =
        (h ^ k) 0 0 • Pi.single (Sum.inl j) 1 + (h ^ k) 1 0 • Pi.single (Sum.inr j) 1 ∧
      M ^ k *ᵥ Pi.single (Sum.inr j) 1 =
        (h ^ k) 0 1 • Pi.single (Sum.inl j) 1 + (h ^ k) 1 1 • Pi.single (Sum.inr j) 1 := by
  let M := mat m F u
  let h : Matrix (Fin 2) (Fin 2) F := !![M (Sum.inl j) (Sum.inl j),
      M (Sum.inl j) (Sum.inr j); M (Sum.inr j) (Sum.inl j), M (Sum.inr j) (Sum.inr j)]
  let e1 : Fin m ⊕ Fin m → F := Pi.single (Sum.inl j) 1
  let e2 : Fin m ⊕ Fin m → F := Pi.single (Sum.inr j) 1
  obtain ⟨hM_e1, hM_e2⟩ := block_action_of_commute_lam htr hu
  dsimp only
  intro k
  induction k with
  | zero =>
    constructor
    · rw [pow_zero, Matrix.one_mulVec]
      funext r
      show e1 r = ((1 : Matrix (Fin 2) (Fin 2) F) 0 0 • e1 +
        (1 : Matrix (Fin 2) (Fin 2) F) 1 0 • e2) r
      simp [e1, e2]
    · rw [pow_zero, Matrix.one_mulVec]
      funext r
      show e2 r = ((1 : Matrix (Fin 2) (Fin 2) F) 0 1 • e1 +
        (1 : Matrix (Fin 2) (Fin 2) F) 1 1 • e2) r
      simp [e1, e2]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · rw [pow_succ, ← Matrix.mulVec_mulVec, hM_e1, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, ih1, ih2, pow_succ]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      module
    · rw [pow_succ, ← Matrix.mulVec_mulVec, hM_e2, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, ih1, ih2, pow_succ]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      module

private theorem block_pow_eq_one_of_commute_lam [CharP F 2] {m : ℕ} {j : Fin m}
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {u : StatedSp m F} (hu : u * lam j g = lam j g * u) {e : ℕ} (h2 : u ^ 2 ^ e = 1) :
    let h : Matrix (Fin 2) (Fin 2) F := !![mat m F u (Sum.inl j) (Sum.inl j),
        mat m F u (Sum.inl j) (Sum.inr j); mat m F u (Sum.inr j) (Sum.inl j),
        mat m F u (Sum.inr j) (Sum.inr j)]
    h ^ 2 ^ e = 1 := by
  let M := mat m F u
  let h : Matrix (Fin 2) (Fin 2) F := !![M (Sum.inl j) (Sum.inl j),
      M (Sum.inl j) (Sum.inr j); M (Sum.inr j) (Sum.inl j), M (Sum.inr j) (Sum.inr j)]
  have hpow := block_pow_eq_of_commute_lam htr hu
  have hM_pow : M ^ 2 ^ e = 1 := by
    have h := congrArg (mat m F) h2
    rwa [map_pow, map_one] at h
  have h1 := (hpow (2 ^ e)).1
  rw [hM_pow, Matrix.one_mulVec] at h1
  have h2' := (hpow (2 ^ e)).2
  rw [hM_pow, Matrix.one_mulVec] at h2'
  ext i k
  fin_cases i <;> fin_cases k <;> simp only [Matrix.one_apply]
  · have := congrFun h1 (Sum.inl j)
    simpa [Pi.single] using this.symm
  · have := congrFun h2' (Sum.inl j)
    simpa [Pi.single] using this.symm
  · have := congrFun h1 (Sum.inr j)
    simpa [Pi.single] using this.symm
  · have := congrFun h2' (Sum.inr j)
    simpa [Pi.single] using this.symm

theorem mat_lam_cols_eq_one_of_commute_of_pow_two_pow [CharP F 2] {m : ℕ} {j : Fin m}
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {u : StatedSp m F} (hu : u * lam j g = lam j g * u) {e : ℕ} (h2 : u ^ 2 ^ e = 1) :
    mat m F u *ᵥ Pi.single (Sum.inl j) 1 = Pi.single (Sum.inl j) 1 ∧
    mat m F u *ᵥ Pi.single (Sum.inr j) 1 = Pi.single (Sum.inr j) 1 := by
  let M := mat m F u
  let h : Matrix (Fin 2) (Fin 2) F := !![M (Sum.inl j) (Sum.inl j),
      M (Sum.inl j) (Sum.inr j); M (Sum.inr j) (Sum.inl j), M (Sum.inr j) (Sum.inr j)]
  have hcomm : h * (g : Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F) * h :=
    block_commutes_of_commute_lam hu
  have hpow : h ^ 2 ^ e = 1 := block_pow_eq_one_of_commute_lam htr hu h2
  have h_eq_one : h = 1 :=
    eq_one_of_commute_of_trace_ne_zero_of_pow_two_pow htr hcomm hpow
  dsimp only [h] at h_eq_one
  let e1 : Fin m ⊕ Fin m → F := Pi.single (Sum.inl j) 1
  let e2 : Fin m ⊕ Fin m → F := Pi.single (Sum.inr j) 1
  have hrow_zero := row_zero_of_commute_lam htr hu
  have hM_e1 : M *ᵥ e1 = e1 := by
    have hact := (block_action_of_commute_lam htr hu).1
    rw [h_eq_one] at hact
    simpa [Matrix.one_apply, e1] using hact
  have hM_e2 : M *ᵥ e2 = e2 := by
    have hact := (block_action_of_commute_lam htr hu).2
    rw [h_eq_one] at hact
    simpa [Matrix.one_apply, e2] using hact
  exact ⟨hM_e1, hM_e2⟩

theorem mem_range_spEmbed_of_commute_lam [CharP F 2] {m k : ℕ}
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    (σ : Fin k → Fin m) (hσ : Function.Injective σ) {u : StatedSp m F}
    (hu : ∀ j, j ∉ Set.range σ → u * lam j g = lam j g * u) (h2 : ∃ e : ℕ, u ^ 2 ^ e = 1) :
    u ∈ (spEmbed (K := F) σ hσ).range := by
  rw [range_spEmbed]
  let S : Set (Fin m ⊕ Fin m) := Set.range (Sum.map σ σ)
  have hS : ParClosed S := by
    intro a ha
    rcases ha with ⟨x, rfl⟩
    rcases x with i | i
    · exact ⟨Sum.inr i, rfl⟩
    · exact ⟨Sum.inl i, rfl⟩
  rw [mem_suppGroup_iff hS]
  intro t ht r
  obtain ⟨e, he⟩ := h2
  rcases t with j | j
  · have hj : j ∉ Set.range σ := by
      intro hj
      rcases hj with ⟨i, rfl⟩
      exact ht ⟨Sum.inl i, rfl⟩
    have h := (mat_lam_cols_eq_one_of_commute_of_pow_two_pow htr (hu j hj) he).1
    rw [← mulVec_single_one_apply (mat m F u) (Sum.inl j) r, h, Matrix.one_apply]
    simp [Pi.single, Function.update_apply]
  · have hj : j ∉ Set.range σ := by
      intro hj
      rcases hj with ⟨i, rfl⟩
      exact ht ⟨Sum.inr i, rfl⟩
    have h := (mat_lam_cols_eq_one_of_commute_of_pow_two_pow htr (hu j hj) he).2
    rw [← mulVec_single_one_apply (mat m F u) (Sum.inr j) r, h, Matrix.one_apply]
    simp [Pi.single, Function.update_apply]

end CFSG.StandardType.SpJoin

end
