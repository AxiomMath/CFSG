module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Mat
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatWt
public import CFSG.LocalAnalysis.StandardType.FS81.RootLineRigidAux

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private instance decidableIsSign (s : Fin 6 → ZMod 3) : Decidable (IsSign s) :=
  inferInstanceAs (Decidable (∀ j, s j = 1 ∨ s j = -1))

local instance (priority := high) neZeroThree : NeZero (3 : ℕ) := ⟨by decide⟩

def RowZeroAtZero (A : GL (Fin 6) (ZMod 3)) : Prop :=
  ∀ j : Fin 6, j ≠ 0 → (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 j = 0

def PreservesSumSq (A : GL (Fin 6) (ZMod 3)) : Prop :=
  ∀ v : Fin 6 → ZMod 3, v 0 = 0 →
    ∑ i, ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) i ^ 2 = ∑ i, v i ^ 2

private theorem rowZeroAtZero_one : RowZeroAtZero (1 : GL (Fin 6) (ZMod 3)) := by
  intro j hj
  simp [Ne.symm hj]

private theorem rowZeroAtZero_mul {A B : GL (Fin 6) (ZMod 3)} (hA : RowZeroAtZero A)
    (hB : RowZeroAtZero B) : RowZeroAtZero (A * B) := by
  intro j hj
  rw [Units.val_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single 0]
  · rw [hB j hj, mul_zero]
  · intro k _ hk
    rw [hA k hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ 0) h

private theorem rowZeroAtZero_inv {A : GL (Fin 6) (ZMod 3)} (hA : RowZeroAtZero A) :
    RowZeroAtZero A⁻¹ := by
  have hAA : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
      ((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h00 : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0 *
      ((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0 = 1 := by
    have := congrFun (congrFun hAA 0) 0
    rw [Matrix.mul_apply] at this
    rw [Finset.sum_eq_single 0] at this
    · simpa [Matrix.one_apply] using this
    · intro k _ hk
      rw [hA k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ 0) h
  have hA00 : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h00
    exact zero_ne_one h00
  intro j hj
  have h0j : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0 *
      ((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 j = 0 := by
    have := congrFun (congrFun hAA 0) j
    rw [Matrix.mul_apply] at this
    rw [Finset.sum_eq_single 0] at this
    · rw [Matrix.one_apply, if_neg (Ne.symm hj)] at this
      exact this
    · intro k _ hk
      rw [hA k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ 0) h
  exact (mul_eq_zero.mp h0j).resolve_left hA00

private theorem preservesSumSq_one : PreservesSumSq (1 : GL (Fin 6) (ZMod 3)) := by
  intro v _
  simp

private theorem preservesSumSq_mul {A B : GL (Fin 6) (ZMod 3)} (hA : PreservesSumSq A)
    (hB : PreservesSumSq B) (hBr : RowZeroAtZero B) : PreservesSumSq (A * B) := by
  intro v hv
  have hBv : (((B : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) 0) = 0 := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single 0]
    · rw [hv, mul_zero]
    · intro k _ hk
      rw [hBr k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ 0) h
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  exact (hA ((B : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) hBv).trans (hB v hv)

private theorem preservesSumSq_inv {A : GL (Fin 6) (ZMod 3)} (hA : PreservesSumSq A)
    (hAr : RowZeroAtZero A) : PreservesSumSq A⁻¹ := by
  have hAA : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
      ((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h00 : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0 *
      ((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0 = 1 := by
    have := congrFun (congrFun hAA 0) 0
    rw [Matrix.mul_apply] at this
    rw [Finset.sum_eq_single 0] at this
    · simpa [Matrix.one_apply] using this
    · intro k _ hk
      rw [hAr k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ 0) h
  have hA00 : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h00
    exact zero_ne_one h00
  intro v hv
  have hw : ((((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) 0) = 0 := by
    have hAv : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
        (((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
    have := congrFun hAv 0
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single 0] at this
    · rw [hv] at this
      exact (mul_eq_zero.mp this).resolve_left hA00
    · intro k _ hk
      rw [hAr k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ 0) h
  have hwq := hA (((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) hw
  have hAv : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      (((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  rw [hAv] at hwq
  exact hwq.symm

def rowQuadSubgroup : Subgroup (GL (Fin 6) (ZMod 3)) where
  carrier := {A | RowZeroAtZero A ∧ PreservesSumSq A}
  one_mem' := ⟨rowZeroAtZero_one, preservesSumSq_one⟩
  mul_mem' := fun hA hB => ⟨rowZeroAtZero_mul hA.1 hB.1, preservesSumSq_mul hA.2 hB.2 hB.1⟩
  inv_mem' := fun hA => ⟨rowZeroAtZero_inv hA.1, preservesSumSq_inv hA.2 hA.1⟩

theorem sum_sq_spMat_mulVec {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3)
    (hs : IsSign s) (v : Fin k → ZMod 3) :
    ∑ i, (spMat σ s *ᵥ v) i ^ 2 = ∑ i, v i ^ 2 := by
  rw [spMat_mulVec]
  have hsq1 : (1 : ZMod 3) ^ 2 = 1 := by decide
  have hsqm1 : (-1 : ZMod 3) ^ 2 = 1 := by decide
  have h : ∀ i, (s (σ.symm i) * v (σ.symm i)) ^ 2 = v (σ.symm i) ^ 2 := by
    intro i
    rcases hs (σ.symm i) with h | h
    · rw [h]
      calc ((1 : ZMod 3) * v (σ.symm i)) ^ 2
          = (1 : ZMod 3) ^ 2 * v (σ.symm i) ^ 2 := by ring
        _ = v (σ.symm i) ^ 2 := by rw [hsq1, one_mul]
    · rw [h]
      calc ((-1 : ZMod 3) * v (σ.symm i)) ^ 2
          = (-1 : ZMod 3) ^ 2 * v (σ.symm i) ^ 2 := by ring
        _ = v (σ.symm i) ^ 2 := by rw [hsqm1, one_mul]
  calc ∑ i, (s (σ.symm i) * v (σ.symm i)) ^ 2
      = ∑ i, v (σ.symm i) ^ 2 := Finset.sum_congr rfl (fun i _ => h i)
    _ = ∑ i, v i ^ 2 := Equiv.sum_comp σ.symm (fun i => v i ^ 2)

private theorem evenAll0_mem_rowQuadSubgroup {A : GL (Fin 6) (ZMod 3)}
    (hA : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ evenAll0 5) : A ∈ rowQuadSubgroup := by
  rcases hA with ⟨σ, s, hs, ⟨hσ0, hprod⟩, hAeq⟩
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [hAeq, spMat_apply]
    by_cases h : 0 = σ j
    · have hj0 : j = 0 := by
        have h1 : σ.symm 0 = σ.symm (σ j) := congrArg σ.symm h
        rw [Equiv.symm_apply_apply] at h1
        have h2 : σ.symm 0 = 0 := by
          have h := Equiv.symm_apply_apply σ 0
          rwa [hσ0] at h
        rw [h2] at h1
        exact h1.symm
      exact absurd hj0 hj
    · simp [h]
  · intro v hv
    rw [hAeq]
    exact sum_sq_spMat_mulVec σ s hs v

private theorem rowZeroAtZero_rE6_matrix (ε : ZMod 3) :
    ∀ j : Fin 6, j ≠ 0 → rE6 ε 0 j = 0 := by
  intro j hj
  simp only [rE6, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  fin_cases j <;> simp_all

variable {k : ℕ}

theorem spMat_eq_perm_mul_diagonal (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) :
    spMat σ s = spMat σ (fun _ => 1) * Matrix.diagonal s := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [spMat_apply, spMat_apply]
    by_cases h : i = σ j <;> simp [h]
  · intro l _ hl
    rw [Matrix.diagonal_apply_ne _ hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem spMat_one_eq_permMatrix (σ : Equiv.Perm (Fin k)) :
    spMat σ (fun _ => 1) = Equiv.Perm.permMatrix (ZMod 3) σ.symm := by
  ext i j
  rw [spMat_apply]
  change (if i = σ j then (1 : ZMod 3) else 0)
    = ((σ.symm).toPEquiv.toMatrix) i j
  have h : ((σ.symm).toPEquiv.toMatrix : Matrix (Fin k) (Fin k) (ZMod 3)) i =
      Pi.single (σ.symm i) (1 : ZMod 3) := PEquiv.toMatrix_toPEquiv_apply σ.symm i
  rw [congrFun h j, Pi.single_apply]
  by_cases hij : i = σ j
  · subst hij
    rw [if_pos rfl, if_pos (Equiv.symm_apply_apply σ j).symm]
  · have hne : j ≠ σ.symm i := fun hh => hij (by rw [← Equiv.apply_symm_apply σ i, hh])
    rw [if_neg hij, if_neg hne]

theorem det_spMat (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) :
    (spMat σ s).det = (Equiv.Perm.sign σ : ZMod 3) * ∏ j, s j := by
  conv_lhs => rw [spMat_eq_perm_mul_diagonal]
  rw [Matrix.det_mul, spMat_one_eq_permMatrix, Matrix.det_permutation,
    Equiv.Perm.sign_symm, Matrix.det_diagonal]

theorem det_spMat_ne_zero (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3)
    (hs : IsSign s) : (spMat σ s).det ≠ 0 := by
  rw [det_spMat]
  have hprod : ∏ j, s j ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j _
    rcases hs j with h | h <;> rw [h] <;> decide
  have hsign : (Equiv.Perm.sign σ : ZMod 3) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> decide
  exact mul_ne_zero hsign hprod

noncomputable def spMatGL (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3)
    (hs : IsSign s) : GL (Fin k) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (spMat σ s) (det_spMat_ne_zero σ s hs)

theorem spMatGL_val (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) (hs : IsSign s) :
    ((spMatGL σ s hs : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) =
      spMat σ s := by
  rw [spMatGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

noncomputable def rE6GL (ε : ZMod 3) (h : (rE6 ε).det ≠ 0) : GL (Fin 6) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rE6 ε) h

theorem rE6GL_val (ε : ZMod 3) (h : (rE6 ε).det ≠ 0) :
    ((rE6GL ε h : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = rE6 ε := by
  rw [rE6GL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

theorem det_rE6_one : (rE6 1).det ≠ 0 := by decide +kernel

theorem det_rE6_neg : (rE6 (-1)).det ≠ 0 := by decide +kernel

private theorem quad_rE6_one :
    ∀ v : Fin 6 → ZMod 3, v 0 = 0 →
      ∑ i, (rE6 1 *ᵥ v) i ^ 2 = ∑ i, v i ^ 2 := by
  decide +kernel

private theorem quad_rE6_neg :
    ∀ v : Fin 6 → ZMod 3, v 0 = 0 →
      ∑ i, (rE6 (-1) *ᵥ v) i ^ 2 = ∑ i, v i ^ 2 := by
  decide +kernel

private theorem rE6_mem_rowQuadSubgroup_one : rE6GL 1 det_rE6_one ∈ rowQuadSubgroup := by
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [rE6GL_val]
    exact rowZeroAtZero_rE6_matrix 1 j hj
  · intro v hv
    rw [rE6GL_val]
    exact quad_rE6_one v hv

private theorem rE6_mem_rowQuadSubgroup_neg : rE6GL (-1) det_rE6_neg ∈ rowQuadSubgroup := by
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [rE6GL_val]
    exact rowZeroAtZero_rE6_matrix (-1) j hj
  · intro v hv
    rw [rE6GL_val]
    exact quad_rE6_neg v hv

private theorem oE6_le_rowQuadSubgroup (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    oE6 ε ≤ rowQuadSubgroup := by
  rw [oE6, Subgroup.closure_le]
  intro A hA
  rcases hA with hA | hA
  · exact evenAll0_mem_rowQuadSubgroup hA
  · rcases hε with rfl | hneg
    · have hdet : (rE6 1).det ≠ 0 := det_rE6_one
      have hAeq : A = rE6GL 1 hdet := by
        apply Units.ext
        rw [hA, rE6GL_val]
      rw [hAeq]
      exact rE6_mem_rowQuadSubgroup_one
    · subst hneg
      have hdet : (rE6 (-1)).det ≠ 0 := det_rE6_neg
      have hAeq : A = rE6GL (-1) hdet := by
        apply Units.ext
        rw [hA, rE6GL_val]
      rw [hAeq]
      exact rE6_mem_rowQuadSubgroup_neg

theorem oE6_rowZeroAtZero (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    ∀ A ∈ oE6 ε, RowZeroAtZero A :=
  fun _A hA => (oE6_le_rowQuadSubgroup ε hε hA).1

theorem oE6_preservesSumSq (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    ∀ A ∈ oE6 ε, PreservesSumSq A :=
  fun _A hA => (oE6_le_rowQuadSubgroup ε hε hA).2

abbrev oE6OrbitSet (ε : ZMod 3) : Set (Fin 6 → ZMod 3) :=
  {e | (wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε)}

private theorem wt_single_one (k : Fin 6) : wt (Pi.single k (1 : ZMod 3)) = 1 := by
  rw [wt]
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext i
  by_cases hi : i = k
  · subst hi
    simp
  · simp [hi]

private theorem wt_neg_single_one (k : Fin 6) : wt (-(Pi.single k (1 : ZMod 3))) = 1 := by
  rw [wt_neg, wt_single_one]

private theorem wt_one_eq_single {e : Fin 6 → ZMod 3} (hwt : wt e = 1) (he0 : e 0 ≠ 0) :
    e = Pi.single 0 1 ∨ e = -(Pi.single 0 1) := by
  have hsupp : Finset.univ.filter (fun i : Fin 6 => e i ≠ 0) = {0} := by
    have hcard : (Finset.univ.filter (fun i : Fin 6 => e i ≠ 0)).card = 1 := hwt
    rw [Finset.card_eq_one] at hcard
    obtain ⟨a, ha⟩ := hcard
    have h0 : (0 : Fin 6) ∈ Finset.univ.filter (fun i : Fin 6 => e i ≠ 0) := by
      simp [he0]
    rw [ha] at h0
    have h0a : (0 : Fin 6) = a := by simpa using h0
    rw [ha, h0a]
  have he : ∀ i : Fin 6, i ≠ 0 → e i = 0 := by
    intro i hi
    by_contra h
    have : i ∈ Finset.univ.filter (fun i : Fin 6 => e i ≠ 0) := by simp [h]
    rw [hsupp] at this
    exact hi (by simpa using this)
  rcases eq_one_or_of_ne_zero he0 with h | h
  · left
    funext i
    by_cases hi : i = 0
    · subst hi; simp [h]
    · rw [he i hi]; simp [hi]
  · right
    funext i
    by_cases hi : i = 0
    · subst hi; simp [h]
    · rw [he i hi]; simp [hi]

private theorem oE6OrbitSet_e0 (ε : ZMod 3) : (Pi.single 0 1 : Fin 6 → ZMod 3) ∈ oE6OrbitSet ε := by
  left
  refine ⟨?_, ?_⟩
  · rw [wt_single_one]; decide
  · simp

private theorem oE6OrbitSet_neg_e0 (ε : ZMod 3) :
    (-(Pi.single 0 1) : Fin 6 → ZMod 3) ∈ oE6OrbitSet ε := by
  left
  refine ⟨?_, ?_⟩
  · rw [wt_neg_single_one]; decide
  · simp

private theorem prod_spMat_mulVec {k : ℕ} (σ : Equiv.Perm (Fin k)) (s v : Fin k → ZMod 3) :
    ∏ i, (spMat σ s *ᵥ v) i = (∏ i, s i) * ∏ i, v i := by
  rw [spMat_mulVec]
  rw [Finset.prod_mul_distrib]
  congr 1
  · exact Equiv.prod_comp σ.symm (fun i => s i)
  · exact Equiv.prod_comp σ.symm (fun i => v i)

private theorem spMat_maps_oE6OrbitSet {ε : ZMod 3} {σ : Equiv.Perm (Fin 6)} {s : Fin 6 → ZMod 3}
    (hs : IsSign s) (hσ0 : σ 0 = 0) (hprod : ∏ i, s i = 1) :
    ∀ e : Fin 6 → ZMod 3, (e ∈ oE6OrbitSet ε) ↔ (spMat σ s *ᵥ e ∈ oE6OrbitSet ε) := by
  intro e
  have hwt : wt (spMat σ s *ᵥ e) = wt e := wt_spMat_mulVec hs e
  have hzero : (spMat σ s *ᵥ e) 0 ≠ 0 ↔ e 0 ≠ 0 := by
    rw [spMat_mulVec]
    change s (σ.symm 0) * e (σ.symm 0) ≠ 0 ↔ e 0 ≠ 0
    have hs0 : σ.symm 0 = 0 := by
      have h := Equiv.symm_apply_apply σ 0
      rwa [hσ0] at h
    rw [hs0]
    have hs0ne : s 0 ≠ 0 := by
      rcases hs 0 with h | h <;> rw [h] <;> decide
    constructor
    · intro h h0
      exact h (by rw [h0, mul_zero])
    · intro h
      exact mul_ne_zero hs0ne h
  have hprod' : ∏ i, (spMat σ s *ᵥ e) i = ∏ i, e i := by
    rw [prod_spMat_mulVec, hprod, one_mul]
  constructor
  · intro h
    rcases h with h | h
    · left
      exact ⟨by rw [hwt]; exact h.1, by rw [hzero]; exact h.2⟩
    · right
      exact ⟨by rw [hwt]; exact h.1, by rw [hprod']; exact h.2⟩
  · intro h
    rcases h with h | h
    · left
      exact ⟨by rw [← hwt]; exact h.1, by rw [← hzero]; exact h.2⟩
    · right
      exact ⟨by rw [← hwt]; exact h.1, by rw [← hprod']; exact h.2⟩

private theorem rE6_maps_oE6OrbitSet_one :
    ∀ e : Fin 6 → ZMod 3, (e ∈ oE6OrbitSet 1) ↔ (rE6 1 *ᵥ e ∈ oE6OrbitSet 1) := by
  decide +kernel

private theorem rE6_maps_oE6OrbitSet_neg :
    ∀ e : Fin 6 → ZMod 3, (e ∈ oE6OrbitSet (-1)) ↔ (rE6 (-1) *ᵥ e ∈ oE6OrbitSet (-1)) := by
  decide +kernel

def oE6OrbitSetStab (ε : ZMod 3) : Subgroup (GL (Fin 6) (ZMod 3)) where
  carrier := {A | ∀ e : Fin 6 → ZMod 3,
    (e ∈ oE6OrbitSet ε) ↔ ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e ∈ oE6OrbitSet ε)}
  one_mem' := by
    intro e
    simp [Matrix.one_mulVec]
  mul_mem' := by
    intro A B hA hB e
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hB e).trans (hA ((B : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e))
  inv_mem' := by
    intro A hA e
    have hAA : (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
        ((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have := hA (((A⁻¹ : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ e)
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec] at this
    exact this.symm

private theorem oE6_le_oE6OrbitSetStab (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    oE6 ε ≤ oE6OrbitSetStab ε := by
  rw [oE6, Subgroup.closure_le]
  intro A hA
  rcases hA with hA | hA
  · rcases hA with ⟨σ, s, hs, ⟨hσ0, hprod⟩, hAeq⟩
    intro e
    rw [hAeq]
    exact spMat_maps_oE6OrbitSet hs hσ0 hprod e
  · rcases hε with rfl | hneg
    · intro e
      rw [hA]
      exact rE6_maps_oE6OrbitSet_one e
    · subst hneg
      intro e
      rw [hA]
      exact rE6_maps_oE6OrbitSet_neg e

theorem orbitE0_subset_oE6OrbitSet (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    ∀ e : Fin 6 → ZMod 3,
      (IsOrbitE0 5 (oE6 ε) e ∨ IsOrbitE0 5 (oE6 ε) (-e)) → e ∈ oE6OrbitSet ε := by
  intro e he
  have hH : ∀ A ∈ oE6 ε, ∀ x : Fin 6 → ZMod 3,
      (x ∈ oE6OrbitSet ε) ↔ ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x ∈ oE6OrbitSet ε) :=
    fun A hA => oE6_le_oE6OrbitSetStab ε hε hA
  rcases he with ⟨A, hA, hAe⟩ | ⟨A, hA, hAe⟩
  · rw [← hAe]
    exact (hH A hA (Pi.single 0 1)).mp (oE6OrbitSet_e0 ε)
  · have hneg : e = (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (-(Pi.single 0 1)) := by
      rw [Matrix.mulVec_neg, hAe, neg_neg]
    rw [hneg]
    exact (hH A hA (-(Pi.single 0 1))).mp (oE6OrbitSet_neg_e0 ε)

private theorem rE6_mem_oE6 (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    ∃ h : (rE6 ε).det ≠ 0, rE6GL ε h ∈ oE6 ε := by
  rcases hε with rfl | hneg
  · refine ⟨det_rE6_one, ?_⟩
    apply Subgroup.subset_closure
    right
    exact rE6GL_val 1 det_rE6_one
  · subst hneg
    refine ⟨det_rE6_neg, ?_⟩
    apply Subgroup.subset_closure
    right
    exact rE6GL_val (-1) det_rE6_neg

private theorem rE6_mulVec_e0_one :
    (rE6 1 *ᵥ (Pi.single 0 1 : Fin 6 → ZMod 3)) = ![1, 1, 1, 1, 1, 1] := by
  decide +kernel

private theorem rE6_mulVec_e0_neg :
    (rE6 (-1) *ᵥ (Pi.single 0 1 : Fin 6 → ZMod 3)) = ![1, 1, 1, 1, 1, -1] := by
  decide +kernel

private theorem exists_diag_full_one :
    ∀ e : Fin 6 → ZMod 3, wt e = 6 → ∏ i, e i = 1 →
      ∃ s : Fin 6 → ZMod 3, IsSign s ∧ ∏ i, s i = 1 ∧
        spMat 1 s *ᵥ (![1, 1, 1, 1, 1, 1] : Fin 6 → ZMod 3) = e := by
  set_option synthInstance.maxSize 512 in
  decide +kernel

private theorem exists_diag_full_neg :
    ∀ e : Fin 6 → ZMod 3, wt e = 6 → ∏ i, e i = -1 →
      ∃ s : Fin 6 → ZMod 3, IsSign s ∧ ∏ i, s i = 1 ∧
        spMat 1 s *ᵥ (![1, 1, 1, 1, 1, -1] : Fin 6 → ZMod 3) = e := by
  set_option synthInstance.maxSize 512 in
  decide +kernel

private theorem fullSupport_orbit_one {e : Fin 6 → ZMod 3} (hwt : wt e = 6)
    (hprod : ∏ i, e i = 1) : IsOrbitE0 5 (oE6 1) e := by
  obtain ⟨s, hs, hprods, hmap⟩ := exists_diag_full_one e hwt hprod
  obtain ⟨hdet, hRmem⟩ := rE6_mem_oE6 1 (Or.inl rfl)
  have hDmem : spMatGL 1 s hs ∈ oE6 1 := by
    apply Subgroup.subset_closure
    left
    exact ⟨1, s, hs, ⟨rfl, hprods⟩, spMatGL_val 1 s hs⟩
  refine ⟨spMatGL 1 s hs * rE6GL 1 hdet, (oE6 1).mul_mem hDmem hRmem, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, rE6GL_val, rE6_mulVec_e0_one, spMatGL_val]
  exact hmap

private theorem fullSupport_orbit_neg {e : Fin 6 → ZMod 3} (hwt : wt e = 6)
    (hprod : ∏ i, e i = -1) : IsOrbitE0 5 (oE6 (-1)) e := by
  obtain ⟨s, hs, hprods, hmap⟩ := exists_diag_full_neg e hwt hprod
  obtain ⟨hdet, hRmem⟩ := rE6_mem_oE6 (-1) (Or.inr rfl)
  have hDmem : spMatGL 1 s hs ∈ oE6 (-1) := by
    apply Subgroup.subset_closure
    left
    exact ⟨1, s, hs, ⟨rfl, hprods⟩, spMatGL_val 1 s hs⟩
  refine ⟨spMatGL 1 s hs * rE6GL (-1) hdet, (oE6 (-1)).mul_mem hDmem hRmem, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, rE6GL_val, rE6_mulVec_e0_neg, spMatGL_val]
  exact hmap

private theorem exists_wt2_one :
    ∀ i : Fin 6, i ≠ 0 → ∀ δ : ZMod 3, (δ = 1 ∨ δ = -1) →
      ∃ s : Fin 6 → ZMod 3, IsSign s ∧ ∏ j, s j = 1 ∧
        spMat (Equiv.swap 5 i) s *ᵥ (![1, 0, 0, 0, 0, -1] : Fin 6 → ZMod 3) =
          Pi.single 0 1 + δ • Pi.single i 1 := by
  decide +kernel

private theorem exists_wt2_neg :
    ∀ i : Fin 6, i ≠ 0 → ∀ δ : ZMod 3, (δ = 1 ∨ δ = -1) →
      ∃ s : Fin 6 → ZMod 3, IsSign s ∧ ∏ j, s j = 1 ∧
        spMat (Equiv.swap 5 i) s *ᵥ (![1, 0, 0, 0, 0, 1] : Fin 6 → ZMod 3) =
          Pi.single 0 1 + δ • Pi.single i 1 := by
  decide +kernel

private theorem wt2_decomp :
    ∀ e : Fin 6 → ZMod 3, wt e = 2 → e 0 ≠ 0 →
      ∃ i : Fin 6, i ≠ 0 ∧ ∃ δ : ZMod 3, (δ = 1 ∨ δ = -1) ∧
        (e = Pi.single 0 1 + δ • Pi.single i 1 ∨
         e = -(Pi.single 0 1 + δ • Pi.single i 1)) := by
  set_option synthInstance.maxSize 512 in
  decide +kernel

private theorem wt2_orbit_aux {ε : ZMod 3} {w : Fin 6 → ZMod 3}
    (hw : IsOrbitE0 5 (oE6 ε) w)
    (hex : ∀ i : Fin 6, i ≠ 0 → ∀ δ : ZMod 3, (δ = 1 ∨ δ = -1) →
      ∃ s : Fin 6 → ZMod 3, IsSign s ∧ ∏ j, s j = 1 ∧
        spMat (Equiv.swap 5 i) s *ᵥ w = Pi.single 0 1 + δ • Pi.single i 1)
    {e : Fin 6 → ZMod 3} (hwt : wt e = 2) (he0 : e 0 ≠ 0) :
    IsOrbitE0 5 (oE6 ε) e ∨ IsOrbitE0 5 (oE6 ε) (-e) := by
  obtain ⟨i, hi, δ, hδ, he | he⟩ := wt2_decomp e hwt he0
  · obtain ⟨s, hs, hprods, hmap⟩ := hex i hi δ hδ
    have hσ0 : Equiv.swap 5 i 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 6) ≠ 5) (Ne.symm hi)
    have hDmem : spMatGL (Equiv.swap 5 i) s hs ∈ oE6 ε := by
      apply Subgroup.subset_closure
      left
      exact ⟨Equiv.swap 5 i, s, hs, ⟨hσ0, hprods⟩, spMatGL_val _ _ _⟩
    have ht : IsOrbitE0 5 (oE6 ε) (Pi.single 0 1 + δ • Pi.single i 1) := by
      obtain ⟨A, hA, hAe⟩ := hw
      refine ⟨spMatGL (Equiv.swap 5 i) s hs * A, (oE6 ε).mul_mem hDmem hA, ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hAe, spMatGL_val]
      exact hmap
    rw [he]
    exact Or.inl ht
  · obtain ⟨s, hs, hprods, hmap⟩ := hex i hi δ hδ
    have hσ0 : Equiv.swap 5 i 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 6) ≠ 5) (Ne.symm hi)
    have hDmem : spMatGL (Equiv.swap 5 i) s hs ∈ oE6 ε := by
      apply Subgroup.subset_closure
      left
      exact ⟨Equiv.swap 5 i, s, hs, ⟨hσ0, hprods⟩, spMatGL_val _ _ _⟩
    have ht : IsOrbitE0 5 (oE6 ε) (Pi.single 0 1 + δ • Pi.single i 1) := by
      obtain ⟨A, hA, hAe⟩ := hw
      refine ⟨spMatGL (Equiv.swap 5 i) s hs * A, (oE6 ε).mul_mem hDmem hA, ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hAe, spMatGL_val]
      exact hmap
    rw [he]
    exact Or.inr (by simpa using ht)

private theorem rE6_mulVec_v'_one :
    (rE6 1 *ᵥ (![1, -1, -1, -1, -1, 1] : Fin 6 → ZMod 3)) =
      ![1, 0, 0, 0, 0, -1] := by
  decide +kernel

private theorem rE6_mulVec_v'_neg :
    (rE6 (-1) *ᵥ (![1, -1, -1, -1, -1, -1] : Fin 6 → ZMod 3)) =
      ![1, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem wt2_orbit_one {e : Fin 6 → ZMod 3} (hwt : wt e = 2) (he0 : e 0 ≠ 0) :
    IsOrbitE0 5 (oE6 1) e ∨ IsOrbitE0 5 (oE6 1) (-e) := by
  have hv' : IsOrbitE0 5 (oE6 1) (![1, -1, -1, -1, -1, 1] : Fin 6 → ZMod 3) :=
    fullSupport_orbit_one (by decide) (by decide)
  have hw : IsOrbitE0 5 (oE6 1) (![1, 0, 0, 0, 0, -1] : Fin 6 → ZMod 3) := by
    obtain ⟨A, hA, hAe⟩ := hv'
    obtain ⟨hdet, hRmem⟩ := rE6_mem_oE6 1 (Or.inl rfl)
    refine ⟨rE6GL 1 hdet * A, (oE6 1).mul_mem hRmem hA, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hAe, rE6GL_val]
    exact rE6_mulVec_v'_one
  exact wt2_orbit_aux hw (fun i hi δ hδ => exists_wt2_one i hi δ hδ) hwt he0

private theorem wt2_orbit_neg {e : Fin 6 → ZMod 3} (hwt : wt e = 2) (he0 : e 0 ≠ 0) :
    IsOrbitE0 5 (oE6 (-1)) e ∨ IsOrbitE0 5 (oE6 (-1)) (-e) := by
  have hv' : IsOrbitE0 5 (oE6 (-1)) (![1, -1, -1, -1, -1, -1] : Fin 6 → ZMod 3) :=
    fullSupport_orbit_neg (by decide) (by decide)
  have hw : IsOrbitE0 5 (oE6 (-1)) (![1, 0, 0, 0, 0, 1] : Fin 6 → ZMod 3) := by
    obtain ⟨A, hA, hAe⟩ := hv'
    obtain ⟨hdet, hRmem⟩ := rE6_mem_oE6 (-1) (Or.inr rfl)
    refine ⟨rE6GL (-1) hdet * A, (oE6 (-1)).mul_mem hRmem hA, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hAe, rE6GL_val]
    exact rE6_mulVec_v'_neg
  exact wt2_orbit_aux hw (fun i hi δ hδ => exists_wt2_neg i hi δ hδ) hwt he0

theorem oE6OrbitSet_subset_orbitE0 (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    ∀ e : Fin 6 → ZMod 3, e ∈ oE6OrbitSet ε → e ≠ 0 →
      IsOrbitE0 5 (oE6 ε) e ∨ IsOrbitE0 5 (oE6 ε) (-e) := by
  intro e he hne
  rcases hε with rfl | hneg
  · rcases he with h | h
    ·
      rcases Nat.lt_or_eq_of_le h.1 with hlt | heq
      · have hwt0 : wt e ≠ 0 := by
          intro h0
          exact hne ((RootLineAux.wt_eq_zero_iff).mp h0)
        have hwt1 : wt e = 1 := by omega
        rcases wt_one_eq_single hwt1 h.2 with rfl | rfl
        · exact Or.inl ⟨1, (oE6 1).one_mem, by rw [Units.val_one, Matrix.one_mulVec]⟩
        · exact Or.inr ⟨1, (oE6 1).one_mem,
            by rw [Units.val_one, Matrix.one_mulVec, neg_neg]⟩
      · have hwt2 : wt e = 2 := by omega
        exact wt2_orbit_one hwt2 h.2
    · exact Or.inl (fullSupport_orbit_one h.1 h.2)
  · subst hneg
    rcases he with h | h
    · rcases Nat.lt_or_eq_of_le h.1 with hlt | heq
      · have hwt0 : wt e ≠ 0 := by
          intro h0
          exact hne ((RootLineAux.wt_eq_zero_iff).mp h0)
        have hwt1 : wt e = 1 := by omega
        rcases wt_one_eq_single hwt1 h.2 with rfl | rfl
        · exact Or.inl ⟨1, (oE6 (-1)).one_mem, by rw [Units.val_one, Matrix.one_mulVec]⟩
        · exact Or.inr ⟨1, (oE6 (-1)).one_mem,
            by rw [Units.val_one, Matrix.one_mulVec, neg_neg]⟩
      · have hwt2 : wt e = 2 := by omega
        exact wt2_orbit_neg hwt2 h.2
    · exact Or.inl (fullSupport_orbit_neg h.1 h.2)

theorem oE6_orbitE0 (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    ∀ e : Fin 6 → ZMod 3, e ≠ 0 →
      ((IsOrbitE0 5 (oE6 ε) e ∨ IsOrbitE0 5 (oE6 ε) (-e)) ↔
        ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε))) := by
  intro e hne
  constructor
  · intro h
    exact orbitE0_subset_oE6OrbitSet ε hε e h
  · intro h
    exact oE6OrbitSet_subset_orbitE0 ε hε e h hne

theorem oE6RecOut_holds : OE6RecOut := by
  intro ε hε
  refine ⟨fun A hA => oE6_rowZeroAtZero ε hε A hA,
    fun A hA => oE6_preservesSumSq ε hε A hA, ?_⟩
  intro e hne
  exact oE6_orbitE0 ε hε e hne

end CFSG.StandardType.FrameRoute.FS81

end
