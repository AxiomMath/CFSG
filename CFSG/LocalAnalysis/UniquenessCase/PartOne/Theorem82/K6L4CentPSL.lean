module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import TauCeti.LinearAlgebra.Matrix.Diagonal
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open Matrix CFSG.Open Subgroup
open CFSG.Open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open.StatedAPI

local notation "pRank" => CFSG.Open.pRank

variable {K : Type} [Field K] [Finite K]

def cent1_A (ζ : CubeRoot K) : Fin 4 → K :=
  fun i => if (i : ℕ) < 2 then (ζ.ω : K) else ((ζ.ω)⁻¹ : K)

theorem cent1_omega_sq_eq_inv (ζ : CubeRoot K) : ζ.ω ^ 2 = (ζ.ω)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ]
  simpa using ζ.pow_three

theorem cent1_omega_ne_inv (ζ : CubeRoot K) : ζ.ω ≠ (ζ.ω)⁻¹ := by
  rw [← cent1_omega_sq_eq_inv ζ]
  intro h
  have h1 : ζ.ω = 1 := by
    have h3 := congrArg (fun x => (ζ.ω)⁻¹ * x) h
    rw [inv_mul_cancel] at h3
    have h4 : (ζ.ω)⁻¹ * ζ.ω ^ 2 = ζ.ω := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h4] at h3
    exact h3.symm
  exact ζ.ne_one h1

theorem cent1_d₁_aux (ζ : CubeRoot K) :
    ((d₁ ζ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal
        (fun i => ((ζ.pow (![1, 1, -1, -1] i - ∑ j, ![1, 1, -1, -1] j) : Kˣ) : K)) := rfl

theorem cent1_pow_one (ζ : CubeRoot K) : ζ.pow (1 : ZMod 3) = ζ.ω := by
  rw [CubeRoot.pow, show (1 : ZMod 3).val = 1 from by decide, pow_one]

theorem cent1_pow_neg_one (ζ : CubeRoot K) : ζ.pow (-1 : ZMod 3) = (ζ.ω)⁻¹ := by
  rw [CubeRoot.pow, show (-1 : ZMod 3).val = 2 from by decide, cent1_omega_sq_eq_inv]

theorem cent1_d₁_eq_diagonal (ζ : CubeRoot K) :
    ((d₁ ζ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (cent1_A ζ) := by
  rw [cent1_d₁_aux]
  congr 1
  funext i
  have h0 : ((1 : ZMod 3) - ∑ j, ![1, 1, -1, -1] j) = 1 := by decide
  have h2 : ((-1 : ZMod 3) - ∑ j, ![1, 1, -1, -1] j) = -1 := by decide
  fin_cases i <;>
    simp [cent1_A, cent1_pow_one, cent1_pow_neg_one, Units.val_inv_eq_inv_val, h0, h2]

theorem cent1_mul_diagonal_comm_iff (A : Fin 4 → K) (g : Matrix (Fin 4) (Fin 4) K) :
    g * Matrix.diagonal A = Matrix.diagonal A * g ↔
      ∀ i j, g i j * (A j - A i) = 0 := by
  constructor
  · intro h i j
    have hh := congrFun (congrFun h i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
    rw [mul_sub, hh, sub_eq_zero]
    exact mul_comm _ _
  · intro h
    ext i j
    have hh := h i j
    rw [mul_sub, sub_eq_zero] at hh
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact hh.trans (mul_comm _ _)

@[expose] def cent1_blk4 (X Y : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks X 0 0 Y)

theorem cent1_blk4_mul (X X' Y Y' : Matrix (Fin 2) (Fin 2) K) :
    cent1_blk4 X Y * cent1_blk4 X' Y' = cent1_blk4 (X * X') (Y * Y') := by
  rw [cent1_blk4, cent1_blk4, cent1_blk4, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem cent1_blk4_one : cent1_blk4 (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [cent1_blk4, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem cent1_det_blk4 (X Y : Matrix (Fin 2) (Fin 2) K) :
    (cent1_blk4 X Y).det = X.det * Y.det := by
  rw [cent1_blk4, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

theorem cent1_blk4_inj {X X' Y Y' : Matrix (Fin 2) (Fin 2) K}
    (h : cent1_blk4 X Y = cent1_blk4 X' Y') : X = X' ∧ Y = Y' := by
  rw [cent1_blk4, cent1_blk4] at h
  have h' := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h
  rw [Matrix.fromBlocks_inj] at h'
  exact ⟨h'.1, h'.2.2.2⟩

def cent1_scalarMat (c : K) : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal fun _ => c

@[expose] noncomputable def cent1_diagGL (a b : GL (Fin 2) K) : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (cent1_blk4 (a : Matrix (Fin 2) (Fin 2) K)
      (b : Matrix (Fin 2) (Fin 2) K))
    (by rw [cent1_det_blk4]
        exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero a)
          (Matrix.GeneralLinearGroup.det_ne_zero b))

theorem cent1_coe_diagGL (a b : GL (Fin 2) K) :
    ((cent1_diagGL a b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      cent1_blk4 (a : Matrix (Fin 2) (Fin 2) K) (b : Matrix (Fin 2) (Fin 2) K) := by
  rw [cent1_diagGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

theorem cent1_diagGL_mul (a b a' b' : GL (Fin 2) K) :
    cent1_diagGL a b * cent1_diagGL a' b' = cent1_diagGL (a * a') (b * b') := by
  apply Units.ext
  rw [Units.val_mul, cent1_coe_diagGL, cent1_coe_diagGL, cent1_coe_diagGL, cent1_blk4_mul]
  congr 1 <;> rw [Units.val_mul]

theorem cent1_diagGL_one : (cent1_diagGL (1 : GL (Fin 2) K) 1) = 1 := by
  apply Units.ext
  rw [cent1_coe_diagGL, Units.val_one, Units.val_one, cent1_blk4_one]

theorem cent1_det_diagGL (a b : GL (Fin 2) K) :
    ((cent1_diagGL a b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
      (a : Matrix (Fin 2) (Fin 2) K).det * (b : Matrix (Fin 2) (Fin 2) K).det := by
  rw [cent1_coe_diagGL, cent1_det_blk4]

theorem cent1_diagGL_inj {a b a' b' : GL (Fin 2) K}
    (h : cent1_diagGL a b = cent1_diagGL a' b') : a = a' ∧ b = b' := by
  have hh := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) h
  rw [cent1_coe_diagGL, cent1_coe_diagGL] at hh
  obtain ⟨h1, h2⟩ := cent1_blk4_inj hh
  exact ⟨Units.ext h1, Units.ext h2⟩

theorem cent1_exists_blk4_of_comm {a b : K} (hab : a ≠ b) {g : Matrix (Fin 4) (Fin 4) K}
    (h : g * cent1_blk4 (cent1_scalarMat a) (cent1_scalarMat b) =
      cent1_blk4 (cent1_scalarMat a) (cent1_scalarMat b) * g) :
    ∃ X Y, g = cent1_blk4 X Y := by
  let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
  obtain ⟨g', rfl⟩ := (Matrix.reindexAlgEquiv K K e).surjective g
  have h1 : cent1_blk4 (cent1_scalarMat a) (cent1_scalarMat b) =
      Matrix.reindexAlgEquiv K K e
        (Matrix.fromBlocks (cent1_scalarMat a) 0 0 (cent1_scalarMat b)) := by
    rw [cent1_blk4, Matrix.coe_reindexAlgEquiv]
  have h' : g' * Matrix.fromBlocks (cent1_scalarMat a) 0 0 (cent1_scalarMat b) =
      Matrix.fromBlocks (cent1_scalarMat a) 0 0 (cent1_scalarMat b) * g' := by
    apply (Matrix.reindexAlgEquiv K K e).injective
    simp only [map_mul, ← h1]
    exact h
  rw [← Matrix.fromBlocks_toBlocks g'] at h'
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h'
  obtain ⟨-, h12, h21, -⟩ := Matrix.fromBlocks_inj.mp h'
  have h12' : g'.toBlocks₁₂ = 0 := by
    ext i j
    have hh := congrFun (congrFun h12 i) j
    simp only [cent1_scalarMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
    have : g'.toBlocks₁₂ i j * (b - a) = 0 := by
      rw [mul_sub, hh, sub_eq_zero]
      exact mul_comm _ _
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hab.symm)
  have h21' : g'.toBlocks₂₁ = 0 := by
    ext i j
    have hh := congrFun (congrFun h21 i) j
    simp only [cent1_scalarMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
    have : g'.toBlocks₂₁ i j * (a - b) = 0 := by
      rw [mul_sub, hh]
      rw [sub_eq_zero]
      exact mul_comm _ _
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hab)
  refine ⟨g'.toBlocks₁₁, g'.toBlocks₂₂, ?_⟩
  rw [cent1_blk4, Matrix.coe_reindexAlgEquiv]
  have hg' : g' = Matrix.fromBlocks g'.toBlocks₁₁ 0 0 g'.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks g']
    rw [h12', h21']
  rw [hg']
  simp [Matrix.fromBlocks_toBlocks]
  rfl

theorem cent1_exists_diagGL_of_comm {a b : K} (hab : a ≠ b) {g : GL (Fin 4) K}
    (hg : g ∈ StatedSL 4 K)
    (hc : (g : Matrix (Fin 4) (Fin 4) K) * cent1_blk4 (cent1_scalarMat a) (cent1_scalarMat b) =
      cent1_blk4 (cent1_scalarMat a) (cent1_scalarMat b) * (g : Matrix (Fin 4) (Fin 4) K)) :
    ∃ p q : GL (Fin 2) K, g = cent1_diagGL p q ∧
      (p : Matrix (Fin 2) (Fin 2) K).det * (q : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  obtain ⟨A, B, hAB⟩ := cent1_exists_blk4_of_comm hab hc
  have hdet : (g : Matrix (Fin 4) (Fin 4) K).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp hg
  have hdetAB : A.det * B.det = 1 := by
    rw [← cent1_det_blk4, ← hAB, hdet]
  have hA : A.det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hdetAB; exact one_ne_zero hdetAB.symm
  have hB : B.det ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdetAB; exact one_ne_zero hdetAB.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA,
    Matrix.GeneralLinearGroup.mkOfDetNeZero B hB, ?_, ?_⟩
  · apply Units.ext
    rw [cent1_coe_diagGL]
    rw [hAB]
    congr 1 <;> exact (Matrix.GeneralLinearGroup.val_mkOfDetNeZero).symm
  · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact hdetAB

theorem cent1_statedSL_comm_iff (g h : StatedSL 4 K) :
    g * h = h * g ↔
      (g : GL (Fin 4) K) * (h : GL (Fin 4) K) = (h : GL (Fin 4) K) * (g : GL (Fin 4) K) := by
  rw [Subtype.ext_iff]
  rfl

theorem cent1_two_ne_zero {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r) :
    (2 : K) ≠ 0 := by
  let := Fintype.ofFinite K
  apply Ring.two_ne_zero
  intro hrc
  have he : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two hrc
  have hodd : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.odd_iff.mp (hr.odd_of_ne_two (by omega))
  omega

theorem cent1_factorization {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    (r * ((r - 1) * (r ^ 2 - 1)) * (r * (r ^ 2 - 1))).factorization r = 2 := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hA : r - 1 ≠ 0 := by omega
  have hr2 : 1 < r ^ 2 := by nlinarith [hr.two_le]
  have hB2 : r ^ 2 - 1 ≠ 0 := by omega
  have h1 : ¬ r ∣ r - 1 :=
    Nat.not_dvd_of_pos_of_lt (n := r - 1) (m := r) (by omega) (by omega)
  have h2 : ¬ r ∣ r ^ 2 - 1 := by
    intro hdvd
    have h1' : r ∣ r ^ 2 - (r ^ 2 - 1) := by
      have hh := Nat.dvd_sub (dvd_mul_right r r) hdvd
      rwa [← pow_two] at hh
    rw [Nat.sub_sub_self (show 1 ≤ r ^ 2 by omega)] at h1'
    exact hr.not_dvd_one h1'
  have hnot : ¬ r ∣ ((r - 1) * (r ^ 2 - 1)) * (r ^ 2 - 1) :=
    hr.not_dvd_mul (hr.not_dvd_mul h1 h2) h2
  rw [show r * ((r - 1) * (r ^ 2 - 1)) * (r * (r ^ 2 - 1)) =
      (r * r) * (((r - 1) * (r ^ 2 - 1)) * (r ^ 2 - 1)) by ac_rfl, ← pow_two]
  rw [Nat.factorization_mul (pow_ne_zero 2 hr0) (mul_ne_zero (mul_ne_zero hA hB2) hB2),
    Finsupp.add_apply, Nat.factorization_pow_self hr, Nat.factorization_eq_zero_of_not_dvd hnot,
    add_zero]

noncomputable abbrev cent1_sGL (c : Kˣ) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) c

theorem cent1_sGL_comm (c : Kˣ) (p : GL (Fin 2) K) : p * cent1_sGL c = cent1_sGL c * p := by
  have hc : cent1_sGL c ∈ Subgroup.center (GL (Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.mp hc p

theorem cent1_blk4_scalar_diagonal (c d : K) :
    cent1_blk4 (cent1_scalarMat c) (cent1_scalarMat d) =
      Matrix.diagonal (fun i : Fin 4 => if (i : ℕ) < 2 then c else d) := by
  have h0 : finSumFinEquiv.symm (0 : Fin 4) = (Sum.inl 0 : Fin 2 ⊕ Fin 2) := rfl
  have h1 : finSumFinEquiv.symm (1 : Fin 4) = (Sum.inl 1 : Fin 2 ⊕ Fin 2) := rfl
  have h2 : finSumFinEquiv.symm (2 : Fin 4) = (Sum.inr 0 : Fin 2 ⊕ Fin 2) := rfl
  have h3 : finSumFinEquiv.symm (3 : Fin 4) = (Sum.inr 1 : Fin 2 ⊕ Fin 2) := rfl
  ext i j
  rw [cent1_blk4, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, Matrix.of_apply, cent1_scalarMat, Matrix.diagonal, h0, h1, h2, h3]

theorem cent1_d₁_eq_diagGL (ζ : CubeRoot K) :
    d₁ ζ = cent1_diagGL (cent1_sGL ζ.ω) (cent1_sGL (ζ.ω)⁻¹) := by
  apply Units.ext
  rw [cent1_coe_diagGL, cent1_d₁_eq_diagonal]
  change Matrix.diagonal (cent1_A ζ) =
    cent1_blk4 (cent1_scalarMat (ζ.ω : K)) (cent1_scalarMat (((ζ.ω)⁻¹ : Kˣ) : K))
  rw [cent1_blk4_scalar_diagonal]
  congr 1
  funext i
  simp [cent1_A]

theorem cent1_diagGL_comm_d₁ (ζ : CubeRoot K) (p q : GL (Fin 2) K) :
    cent1_diagGL p q * d₁ ζ = d₁ ζ * cent1_diagGL p q := by
  rw [cent1_d₁_eq_diagGL, cent1_diagGL_mul, cent1_diagGL_mul, cent1_sGL_comm, cent1_sGL_comm]

theorem cent1_sl_det (h : StatedSL 2 K) :
    Matrix.GeneralLinearGroup.det (h : GL (Fin 2) K) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    CFSG.Open.StatedAPI.det_of_mem_statedSL h.2, Units.val_one]

theorem cent1_det_diagGL_unit (a b : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.det (cent1_diagGL a b) =
      Matrix.GeneralLinearGroup.det a * Matrix.GeneralLinearGroup.det b := by
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact cent1_det_diagGL a b

theorem cent1_card_centralizer_det (ζ : CubeRoot K) (p : GL (Fin 2) K) (q : StatedSL 2 K) :
    cent1_diagGL p (q * p⁻¹) ∈ StatedSL 4 K := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
  have hdet : Matrix.GeneralLinearGroup.det (cent1_diagGL p (q * p⁻¹)) = 1 := by
    rw [cent1_det_diagGL_unit, map_mul, cent1_sl_det q, one_mul, map_inv, mul_inv_cancel]
  rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]

theorem cent1_card_centralizer_comm (ζ : CubeRoot K) {d : StatedSL 4 K}
    (hd : (d : GL (Fin 4) K) = d₁ ζ) (p : GL (Fin 2) K) (q : StatedSL 2 K) :
    (⟨cent1_diagGL p (q * p⁻¹), cent1_card_centralizer_det ζ p q⟩ : StatedSL 4 K) ∈
      Subgroup.centralizer ({d} : Set (StatedSL 4 K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, cent1_statedSL_comm_iff, hd]
  exact cent1_diagGL_comm_d₁ ζ p (q * p⁻¹)

noncomputable def cent1_card_centralizerMap (ζ : CubeRoot K) (h2 : (2 : K) ≠ 0)
    {d : StatedSL 4 K} (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    GL (Fin 2) K × StatedSL 2 K → Subgroup.centralizer ({d} : Set (StatedSL 4 K)) :=
  fun p => ⟨⟨cent1_diagGL p.1 (p.2 * p.1⁻¹), cent1_card_centralizer_det ζ p.1 p.2⟩,
    cent1_card_centralizer_comm ζ hd p.1 p.2⟩

theorem cent1_card_centralizerMap_injective (ζ : CubeRoot K) (h2 : (2 : K) ≠ 0)
    {d : StatedSL 4 K} (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    Function.Injective (cent1_card_centralizerMap ζ h2 hd) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ hp
  have hgl := congrArg (fun g : Subgroup.centralizer ({d} : Set (StatedSL 4 K)) =>
    ((g : StatedSL 4 K) : GL (Fin 4) K)) hp
  obtain ⟨hp1, hp2⟩ := cent1_diagGL_inj hgl
  have hp1' : p = p' := hp1
  have hp2' : q = q' := by
    have hh := congrArg (fun x : GL (Fin 2) K => x * p) hp2
    simp only [mul_assoc, mul_inv_cancel, mul_one] at hh
    rw [hp1', inv_mul_cancel, mul_one] at hh
    exact Subtype.ext (by simpa using hh)
  exact Prod.ext hp1' hp2'

theorem cent1_card_centralizerMap_surjective (ζ : CubeRoot K) (h2 : (2 : K) ≠ 0)
    {d : StatedSL 4 K} (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    Function.Surjective (cent1_card_centralizerMap ζ h2 hd) := by
  rintro ⟨g, hg⟩
  have hcomm : (g : GL (Fin 4) K) * cent1_diagGL (cent1_sGL ζ.ω) (cent1_sGL (ζ.ω)⁻¹) =
      cent1_diagGL (cent1_sGL ζ.ω) (cent1_sGL (ζ.ω)⁻¹) * (g : GL (Fin 4) K) := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [cent1_statedSL_comm_iff, hd, cent1_d₁_eq_diagGL ζ] at h1
    exact h1
  have hcomm' : ((g : StatedSL 4 K) : GL (Fin 4) K) * cent1_blk4 (cent1_scalarMat (ζ.ω : K))
      (cent1_scalarMat (((ζ.ω)⁻¹ : Kˣ) : K)) =
      cent1_blk4 (cent1_scalarMat (ζ.ω : K)) (cent1_scalarMat (((ζ.ω)⁻¹ : Kˣ) : K)) *
        ((g : StatedSL 4 K) : GL (Fin 4) K) := by
    have hh := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hcomm
    simp only [Units.val_mul, cent1_coe_diagGL] at hh
    rwa [show ((cent1_sGL ζ.ω : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          cent1_scalarMat (ζ.ω : K) from rfl,
        show ((cent1_sGL (ζ.ω)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          cent1_scalarMat (((ζ.ω)⁻¹ : Kˣ) : K) from rfl] at hh
  have hω : (ζ.ω : K) ≠ (((ζ.ω)⁻¹ : Kˣ) : K) :=
    fun h => cent1_omega_ne_inv ζ (Units.ext (by simpa using h))
  obtain ⟨p, q, hpq, hdet⟩ :=
    cent1_exists_diagGL_of_comm (a := (ζ.ω : K)) (b := (((ζ.ω)⁻¹ : Kˣ) : K))
      hω (g : StatedSL 4 K).2 hcomm'
  refine ⟨(p, ⟨q * p, ?_⟩), ?_⟩
  · rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    have hdet_unit : Matrix.GeneralLinearGroup.det p * Matrix.GeneralLinearGroup.det q = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.GeneralLinearGroup.val_det_apply]
      exact hdet
    have hq : Matrix.GeneralLinearGroup.det q = (Matrix.GeneralLinearGroup.det p)⁻¹ := by
      have hh := congrArg (fun x => (Matrix.GeneralLinearGroup.det p)⁻¹ * x) hdet_unit
      simpa [mul_assoc] using hh
    have hdet' : Matrix.GeneralLinearGroup.det (q * p) = 1 := by
      rw [map_mul, hq, inv_mul_cancel]
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet', Units.val_one]
  · apply Subtype.ext
    apply Subtype.ext
    change cent1_diagGL p (((⟨q * p, _⟩ : StatedSL 2 K) : GL (Fin 2) K) * p⁻¹) =
      (g : GL (Fin 4) K)
    rw [show ((⟨q * p, _⟩ : StatedSL 2 K) : GL (Fin 2) K) * p⁻¹ = q from by
      rw [mul_assoc, mul_inv_cancel, mul_one]]
    exact hpq.symm

theorem cent1_card_centralizer (ζ : CubeRoot K) (h2 : (2 : K) ≠ 0) {d : StatedSL 4 K}
    (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    Nat.card (Subgroup.centralizer ({d} : Set (StatedSL 4 K))) =
      Nat.card (GL (Fin 2) K) * Nat.card (StatedSL 2 K) := by
  rw [← Nat.card_prod]
  symm
  exact Nat.card_congr (Equiv.ofBijective (cent1_card_centralizerMap ζ h2 hd)
    ⟨cent1_card_centralizerMap_injective ζ h2 hd, cent1_card_centralizerMap_surjective ζ h2 hd⟩)

theorem cent1_card_GL_two {r : ℕ} (hK : Nat.card K = r) :
    Nat.card (GL (Fin 2) K) = r * ((r - 1) * (r ^ 2 - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq (K := K) 2, hK]
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [hIcc, Finset.prod_insert (by decide), Finset.prod_singleton]
  norm_num

theorem cent1_card_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) :
    ∀ d : StatedSL 4 K, (d : GL (Fin 4) K) = d₁ ζ →
      (Nat.card (Subgroup.centralizer ({d} : Set (StatedSL 4 K)))).factorization r = 2 := by
  intro d hd
  have h2 : (2 : K) ≠ 0 := cent1_two_ne_zero hr h5 hK
  rw [cent1_card_centralizer ζ h2 hd, cent1_card_GL_two hK,
    CFSG.Open.StatedAPI.card_statedSL_two, hK]
  exact cent1_factorization hr h5

theorem cent1_transvection_pow {n : Type} [Fintype n] [DecidableEq n]
    (i j : n) (hij : i ≠ j) (c : K) (m : ℕ) :
    (Matrix.transvection i j c) ^ m = Matrix.transvection i j (m • c) := by
  induction m with
  | zero => simp [Matrix.transvection_zero]
  | succ m ih =>
    rw [pow_succ, ih, Matrix.transvection_mul_transvection_same (i := i) (j := j) hij,
      add_nsmul, one_nsmul]

@[expose] def cent1_t : GL (Fin 2) K where
  val := Matrix.transvection (0 : Fin 2) (1 : Fin 2) (1 : K)
  inv := Matrix.transvection (0 : Fin 2) (1 : Fin 2) (-1 : K)
  val_inv := by
    rw [Matrix.transvection_mul_transvection_same (i := (0 : Fin 2)) (j := 1) (by decide)
      (1 : K) (-1 : K), add_neg_cancel, Matrix.transvection_zero]
  inv_val := by
    rw [Matrix.transvection_mul_transvection_same (i := (0 : Fin 2)) (j := 1) (by decide)
      (-1 : K) (1 : K), neg_add_cancel, Matrix.transvection_zero]

theorem cent1_t_val :
    (((cent1_t (K := K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.transvection (0 : Fin 2) (1 : Fin 2) (1 : K) := rfl

theorem cent1_t_pow_val (m : ℕ) :
    (((cent1_t (K := K)) ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.transvection (0 : Fin 2) (1 : Fin 2) (m • (1 : K)) := by
  rw [Units.val_pow_eq_pow_val]
  exact cent1_transvection_pow (n := Fin 2) (K := K) (0 : Fin 2) 1 (by decide) 1 m

theorem cent1_r_eq_zero {r : ℕ} (hK : Nat.card K = r) : (r : K) = 0 := by
  let := Fintype.ofFinite K
  have hcard : Fintype.card K = r := by rw [← Nat.card_eq_fintype_card, hK]
  rw [← hcard]
  exact FiniteField.cast_card_eq_zero K

theorem cent1_nsmul_one_eq_zero {r : ℕ} (hK : Nat.card K = r) : r • (1 : K) = 0 := by
  rw [nsmul_eq_mul, mul_one, cent1_r_eq_zero (K := K) hK]

theorem cent1_t_pow_r {r : ℕ} (hK : Nat.card K = r) : (cent1_t (K := K)) ^ r = 1 := by
  apply Units.ext
  rw [cent1_t_pow_val, cent1_nsmul_one_eq_zero (K := K) hK, Matrix.transvection_zero,
    Units.val_one]

theorem cent1_t_ne_one : (cent1_t (K := K)) ≠ 1 := by
  intro h
  have hh := congrArg (fun u : GL (Fin 2) K =>
    (u : Matrix (Fin 2) (Fin 2) K) (0 : Fin 2) (1 : Fin 2)) h
  rw [cent1_t_val, Matrix.transvection] at hh
  simp at hh

theorem cent1_orderOf_t {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    orderOf (cent1_t (K := K)) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  exact orderOf_eq_prime (cent1_t_pow_r hK) cent1_t_ne_one

@[expose] noncomputable def cent1_blkL : GL (Fin 2) K →* GL (Fin 4) K where
  toFun a := cent1_diagGL a 1
  map_one' := cent1_diagGL_one
  map_mul' a b := by rw [cent1_diagGL_mul, mul_one]

@[expose] noncomputable def cent1_blkR : GL (Fin 2) K →* GL (Fin 4) K where
  toFun a := cent1_diagGL 1 a
  map_one' := cent1_diagGL_one
  map_mul' a b := by rw [cent1_diagGL_mul, one_mul]

theorem cent1_blkL_injective : Function.Injective (cent1_blkL (K := K)) :=
  fun _ _ h => (cent1_diagGL_inj h).1

theorem cent1_blkR_injective : Function.Injective (cent1_blkR (K := K)) :=
  fun _ _ h => (cent1_diagGL_inj h).2

theorem cent1_blkL_mul_blkR_comm (a b : GL (Fin 2) K) :
    cent1_blkL (K := K) a * cent1_blkR (K := K) b =
      cent1_blkR (K := K) b * cent1_blkL (K := K) a := by
  change cent1_diagGL a 1 * cent1_diagGL 1 b = cent1_diagGL 1 b * cent1_diagGL a 1
  rw [cent1_diagGL_mul, cent1_diagGL_mul, mul_one, one_mul, mul_one, one_mul]

theorem cent1_range_inf :
    (cent1_blkL (K := K)).range ⊓ (cent1_blkR (K := K)).range = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzL, hzR⟩
  obtain ⟨a, rfl⟩ := hzL
  obtain ⟨b, hb⟩ := hzR
  have h : a = 1 := (cent1_diagGL_inj (show cent1_diagGL a 1 = cent1_diagGL 1 b from hb.symm)).1
  show cent1_diagGL a 1 ∈ (⊥ : Subgroup (GL (Fin 4) K))
  rw [h, cent1_diagGL_one]
  exact Subgroup.mem_bot.mpr rfl

@[expose] noncomputable def cent1_x : StatedSL 4 K :=
  ⟨cent1_blkL (K := K) (cent1_t (K := K)), by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    show ((cent1_diagGL (cent1_t (K := K)) 1 : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = 1
    rw [cent1_det_diagGL, cent1_t_val,
      Matrix.det_transvection_of_ne (i := (0 : Fin 2)) (j := 1) (by decide) (1 : K)]
    simp⟩

@[expose] noncomputable def cent1_y : StatedSL 4 K :=
  ⟨cent1_blkR (K := K) (cent1_t (K := K)), by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    show ((cent1_diagGL 1 (cent1_t (K := K)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = 1
    rw [cent1_det_diagGL, cent1_t_val,
      Matrix.det_transvection_of_ne (i := (0 : Fin 2)) (j := 1) (by decide) (1 : K)]
    simp⟩

theorem cent1_orderOf_x {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    orderOf (cent1_x (K := K)) = r := by
  simp only [cent1_x, Subgroup.orderOf_mk]
  rw [orderOf_injective (cent1_blkL (K := K)) (cent1_blkL_injective (K := K)),
    cent1_orderOf_t hr hK]

theorem cent1_orderOf_y {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    orderOf (cent1_y (K := K)) = r := by
  simp only [cent1_y, Subgroup.orderOf_mk]
  rw [orderOf_injective (cent1_blkR (K := K)) (cent1_blkR_injective (K := K)),
    cent1_orderOf_t hr hK]

theorem cent1_x_mem (ζ : CubeRoot K) {d : StatedSL 4 K}
    (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    cent1_x (K := K) ∈ Subgroup.centralizer ({d} : Set (StatedSL 4 K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, cent1_statedSL_comm_iff, hd]
  exact cent1_diagGL_comm_d₁ ζ (cent1_t (K := K)) 1

theorem cent1_y_mem (ζ : CubeRoot K) {d : StatedSL 4 K}
    (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    cent1_y (K := K) ∈ Subgroup.centralizer ({d} : Set (StatedSL 4 K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, cent1_statedSL_comm_iff, hd]
  exact cent1_diagGL_comm_d₁ ζ 1 (cent1_t (K := K))

theorem cent1_y_ne_one : (cent1_y (K := K)) ≠ 1 := by
  intro h
  have hgl : cent1_blkR (K := K) (cent1_t (K := K)) = 1 := by
    have := congrArg (fun z : StatedSL 4 K => (z : GL (Fin 4) K)) h
    simpa [cent1_y] using this
  exact cent1_t_ne_one (cent1_blkR_injective (by rw [hgl, map_one]))

theorem cent1_comm_x_y : Commute (cent1_x (K := K)) (cent1_y (K := K)) := by
  show cent1_x (K := K) * cent1_y (K := K) = cent1_y (K := K) * cent1_x (K := K)
  apply Subtype.ext
  change cent1_blkL (K := K) (cent1_t (K := K)) * cent1_blkR (K := K) (cent1_t (K := K)) =
    cent1_blkR (K := K) (cent1_t (K := K)) * cent1_blkL (K := K) (cent1_t (K := K))
  exact cent1_blkL_mul_blkR_comm _ _

theorem cent1_y_not_mem_zpowers_x :
    (cent1_y (K := K)) ∉ Subgroup.zpowers (cent1_x (K := K)) := by
  intro h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  have hL : (cent1_y (K := K) : GL (Fin 4) K) ∈ (cent1_blkL (K := K)).range := by
    rw [← hn]
    exact MonoidHom.mem_range.mpr ⟨(cent1_t (K := K)) ^ n, by
      rw [map_zpow]
      rfl⟩
  have hR : (cent1_y (K := K) : GL (Fin 4) K) ∈ (cent1_blkR (K := K)).range :=
    MonoidHom.mem_range.mpr ⟨cent1_t (K := K), rfl⟩
  have hbot : (cent1_y (K := K) : GL (Fin 4) K) ∈ (⊥ : Subgroup (GL (Fin 4) K)) := by
    rw [← cent1_range_inf]
    exact ⟨hL, hR⟩
  exact cent1_y_ne_one (Subtype.ext (Subgroup.mem_bot.mp hbot))

theorem cent1_pRank_ge {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) {d : StatedSL 4 K} (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    2 ≤ pRank r (Subgroup.centralizer ({d} : Set (StatedSL 4 K))) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hxcard : Nat.card (Subgroup.zpowers (cent1_x (K := K))) = r := by
    rw [Nat.card_zpowers, cent1_orderOf_x hr hK]
  have hcomm : ∀ a ∈ Subgroup.zpowers (cent1_x (K := K)),
      a * cent1_y (K := K) = cent1_y (K := K) * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (cent1_comm_x_y (K := K)).zpow_left n |>.eq
  obtain ⟨hea, hcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (X := Subgroup.zpowers (cent1_x (K := K))) hxcard (cent1_orderOf_y hr hK)
    (cent1_y_not_mem_zpowers_x (K := K)) hcomm
  have hle : Subgroup.zpowers (cent1_x (K := K)) ⊔ Subgroup.zpowers (cent1_y (K := K)) ≤
      Subgroup.centralizer ({d} : Set (StatedSL 4 K)) :=
    sup_le (Subgroup.zpowers_le.mpr (cent1_x_mem ζ hd))
      (Subgroup.zpowers_le.mpr (cent1_y_mem ζ hd))
  exact CFSG.SectionRank.le_pRank hr.one_lt hle hea (by simpa using hcard)

theorem cent1_pRank_le {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) {d : StatedSL 4 K} (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    pRank r (Subgroup.centralizer ({d} : Set (StatedSL 4 K))) ≤ 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hcard := cent1_card_sl hr h5 hK ζ d hd
  refine CFSG.SectionRank.pRank_le (G := StatedSL 4 K) (p := r) hr.one_lt fun E hE hEa => ?_
  have hEpg : IsPGroup r ↥E := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one, orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (hEa.2 (x : StatedSL 4 K) x.2)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEpg
  have hdiv : r ^ k ∣ Nat.card (Subgroup.centralizer ({d} : Set (StatedSL 4 K))) := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le hE
  have hff : (r ^ k).factorization ≤
      (Nat.card (Subgroup.centralizer ({d} : Set (StatedSL 4 K)))).factorization :=
    (Nat.factorization_le_iff_dvd (pow_ne_zero k hr.ne_zero) Nat.card_pos.ne').mpr hdiv
  have hk2 : k ≤ 2 := by
    have := hff r
    rwa [Nat.factorization_pow_self hr, hcard] at this
  rw [hk]
  exact Nat.pow_le_pow_right hr.pos hk2

theorem cent1_rank_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) :
    ∀ d : StatedSL 4 K, (d : GL (Fin 4) K) = d₁ ζ →
      pRank r (Subgroup.centralizer ({d} : Set (StatedSL 4 K))) = 2 := by
  intro d hd
  exact le_antisymm (cent1_pRank_le hr h5 hK ζ hd) (cent1_pRank_ge hr h5 hK ζ hd)

def cent2_A (ζ : CubeRoot K) : Fin 4 → K :=
  fun i => if i = 0 then (ζ.ω : K) else if i = 1 then ((ζ.ω)⁻¹ : K) else 1

theorem cent2_d₂_aux (ζ : CubeRoot K) :
    ((d₂ ζ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal
        (fun i => ((ζ.pow (![1, -1, 0, 0] i - ∑ j, ![1, -1, 0, 0] j) : Kˣ) : K)) := rfl

theorem cent2_d₂_eq_diagonal (ζ : CubeRoot K) :
    ((d₂ ζ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (cent2_A ζ) := by
  rw [cent2_d₂_aux]
  congr 1
  funext i
  have h0 : ((1 : ZMod 3) - ∑ j, ![1, -1, 0, 0] j) = 1 := by decide
  have h1 : ((-1 : ZMod 3) - ∑ j, ![1, -1, 0, 0] j) = -1 := by decide
  have h2 : ((0 : ZMod 3) - ∑ j, ![1, -1, 0, 0] j) = 0 := by decide
  fin_cases i <;>
    simp [cent2_A, cent1_pow_one, cent1_pow_neg_one, CubeRoot.pow_zero, h0, h1, h2]

def cent2_diag (a b : K) : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![a, b]

def cent2_blk (a b : K) (M : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  cent1_blk4 (cent2_diag a b) M

theorem cent2_det_blk (a b : K) (M : Matrix (Fin 2) (Fin 2) K) :
    (cent2_blk a b M).det = a * b * M.det := by
  rw [cent2_blk, cent1_det_blk4, cent2_diag, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem cent2_blk_inj {a b a' b' : K} {M M' : Matrix (Fin 2) (Fin 2) K}
    (h : cent2_blk a b M = cent2_blk a' b' M') : a = a' ∧ b = b' ∧ M = M' := by
  obtain ⟨h1, h2⟩ := cent1_blk4_inj h
  rw [cent2_diag, cent2_diag] at h1
  have h1' := Matrix.diagonal_injective h1
  have hab : (![a, b] : Fin 2 → K) = ![a', b'] := h1'
  refine ⟨?_, ?_, h2⟩
  · simpa using congrFun hab 0
  · simpa using congrFun hab 1

theorem cent2_offdiag_zero (ζ : CubeRoot K) {g : Matrix (Fin 4) (Fin 4) K}
    (h : g * Matrix.diagonal (cent2_A ζ) = Matrix.diagonal (cent2_A ζ) * g) :
    ∀ i j : Fin 4, cent2_A ζ j ≠ cent2_A ζ i → g i j = 0 := by
  rw [cent1_mul_diagonal_comm_iff] at h
  intro i j hij
  exact (mul_eq_zero.mp (h i j)).resolve_right (sub_ne_zero.mpr hij)

theorem cent2_offdiag_zero_left (ζ : CubeRoot K) {g : Matrix (Fin 4) (Fin 4) K}
    (h : g * Matrix.diagonal (cent2_A ζ) = Matrix.diagonal (cent2_A ζ) * g) :
    g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 0 2 = 0 ∧ g 0 3 = 0 ∧ g 1 2 = 0 := by
  have hz := cent2_offdiag_zero ζ h
  have hω : (ζ.ω : K) ≠ (((ζ.ω)⁻¹ : Kˣ) : K) :=
    fun hh => cent1_omega_ne_inv ζ (Units.ext (by simpa using hh))
  have hω1 : (ζ.ω : K) ≠ 1 := fun hh => ζ.ne_one (Units.ext (by simpa using hh))
  have hi1 : (((ζ.ω)⁻¹ : Kˣ) : K) ≠ 1 := by
    intro hh
    apply ζ.ne_one
    have := congrArg (fun x : Kˣ => x⁻¹) (Units.ext (by simpa using hh) : (ζ.ω)⁻¹ = 1)
    simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hz 0 1 (by
      rw [show cent2_A ζ 1 = (((ζ.ω)⁻¹ : Kˣ) : K) from by simp [cent2_A],
        show cent2_A ζ 0 = (ζ.ω : K) from by simp [cent2_A]]
      exact hω.symm)
  · exact hz 1 0 (by
      rw [show cent2_A ζ 1 = (((ζ.ω)⁻¹ : Kˣ) : K) from by simp [cent2_A],
        show cent2_A ζ 0 = (ζ.ω : K) from by simp [cent2_A]]
      exact hω)
  · exact hz 0 2 (by
      rw [show cent2_A ζ 2 = (1 : K) from by simp [cent2_A],
        show cent2_A ζ 0 = (ζ.ω : K) from by simp [cent2_A]]
      exact hω1.symm)
  · exact hz 0 3 (by
      rw [show cent2_A ζ 3 = (1 : K) from by simp [cent2_A],
        show cent2_A ζ 0 = (ζ.ω : K) from by simp [cent2_A]]
      exact hω1.symm)
  · exact hz 1 2 (by
      rw [show cent2_A ζ 1 = (((ζ.ω)⁻¹ : Kˣ) : K) from by simp [cent2_A],
        show cent2_A ζ 2 = (1 : K) from by simp [cent2_A]]
      exact hi1.symm)

theorem cent2_offdiag_zero_right (ζ : CubeRoot K) {g : Matrix (Fin 4) (Fin 4) K}
    (h : g * Matrix.diagonal (cent2_A ζ) = Matrix.diagonal (cent2_A ζ) * g) :
    g 1 3 = 0 ∧ g 2 0 = 0 ∧ g 3 0 = 0 ∧ g 2 1 = 0 ∧ g 3 1 = 0 := by
  have hz := cent2_offdiag_zero ζ h
  have hω1 : (ζ.ω : K) ≠ 1 := fun hh => ζ.ne_one (Units.ext (by simpa using hh))
  have hi1 : (((ζ.ω)⁻¹ : Kˣ) : K) ≠ 1 := by
    intro hh
    apply ζ.ne_one
    have := congrArg (fun x : Kˣ => x⁻¹) (Units.ext (by simpa using hh) : (ζ.ω)⁻¹ = 1)
    simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hz 1 3 (by
      rw [show cent2_A ζ 3 = (1 : K) from by simp [cent2_A],
        show cent2_A ζ 1 = (((ζ.ω)⁻¹ : Kˣ) : K) from by simp [cent2_A]]
      exact hi1.symm)
  · exact hz 2 0 (by
      rw [show cent2_A ζ 0 = (ζ.ω : K) from by simp [cent2_A],
        show cent2_A ζ 2 = (1 : K) from by simp [cent2_A]]
      exact hω1)
  · exact hz 3 0 (by
      rw [show cent2_A ζ 0 = (ζ.ω : K) from by simp [cent2_A],
        show cent2_A ζ 3 = (1 : K) from by simp [cent2_A]]
      exact hω1)
  · exact hz 2 1 (by
      rw [show cent2_A ζ 1 = (((ζ.ω)⁻¹ : Kˣ) : K) from by simp [cent2_A],
        show cent2_A ζ 2 = (1 : K) from by simp [cent2_A]]
      exact hi1)
  · exact hz 3 1 (by
      rw [show cent2_A ζ 1 = (((ζ.ω)⁻¹ : Kˣ) : K) from by simp [cent2_A],
        show cent2_A ζ 3 = (1 : K) from by simp [cent2_A]]
      exact hi1)

theorem cent2_exists_blk_of_comm (ζ : CubeRoot K) {g : Matrix (Fin 4) (Fin 4) K}
    (h : g * Matrix.diagonal (cent2_A ζ) = Matrix.diagonal (cent2_A ζ) * g) :
    ∃ a b M, g = cent2_blk a b M := by
  obtain ⟨h01, h10, h02, h03, h12⟩ := cent2_offdiag_zero_left ζ h
  obtain ⟨h13, h20, h30, h21, h31⟩ := cent2_offdiag_zero_right ζ h
  refine ⟨g 0 0, g 1 1, fun i j => g (Fin.natAdd 2 i) (Fin.natAdd 2 j), ?_⟩
  have h0 : finSumFinEquiv.symm (0 : Fin 4) = (Sum.inl 0 : Fin 2 ⊕ Fin 2) := rfl
  have h1 : finSumFinEquiv.symm (1 : Fin 4) = (Sum.inl 1 : Fin 2 ⊕ Fin 2) := rfl
  have h2 : finSumFinEquiv.symm (2 : Fin 4) = (Sum.inr 0 : Fin 2 ⊕ Fin 2) := rfl
  have h3 : finSumFinEquiv.symm (3 : Fin 4) = (Sum.inr 1 : Fin 2 ⊕ Fin 2) := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cent2_blk, cent1_blk4, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.fromBlocks, Matrix.of_apply, cent2_diag, Matrix.diagonal, h0, h1, h2, h3,
      h01, h10, h02, h03, h12, h13, h20, h30, h21, h31]

theorem cent2_comm_d₂ (ζ : CubeRoot K) (a b : K) (M : Matrix (Fin 2) (Fin 2) K) :
    cent2_blk a b M * Matrix.diagonal (cent2_A ζ) =
      Matrix.diagonal (cent2_A ζ) * cent2_blk a b M := by
  have h0 : finSumFinEquiv.symm (0 : Fin 4) = (Sum.inl 0 : Fin 2 ⊕ Fin 2) := rfl
  have h1 : finSumFinEquiv.symm (1 : Fin 4) = (Sum.inl 1 : Fin 2 ⊕ Fin 2) := rfl
  have h2 : finSumFinEquiv.symm (2 : Fin 4) = (Sum.inr 0 : Fin 2 ⊕ Fin 2) := rfl
  have h3 : finSumFinEquiv.symm (3 : Fin 4) = (Sum.inr 1 : Fin 2 ⊕ Fin 2) := rfl
  rw [cent1_mul_diagonal_comm_iff]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cent2_blk, cent1_blk4, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.fromBlocks, Matrix.of_apply, cent2_diag, Matrix.diagonal, h0, h1, h2, h3,
      cent2_A]

theorem cent2_blk_det_unit (p : Kˣ × GL (Fin 2) K) :
    (cent2_blk (p.1 : K) (((p.1 : K) * (p.2 : Matrix (Fin 2) (Fin 2) K).det)⁻¹)
      (p.2 : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
  rw [cent2_det_blk, mul_inv]
  field_simp [Units.ne_zero p.1, Matrix.GeneralLinearGroup.det_ne_zero p.2]

theorem cent2_card_centralizer_det (ζ : CubeRoot K) (p : Kˣ × GL (Fin 2) K) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (cent2_blk (p.1 : K) (((p.1 : K) * (p.2 : Matrix (Fin 2) (Fin 2) K).det)⁻¹)
          (p.2 : Matrix (Fin 2) (Fin 2) K))
        (by rw [cent2_blk_det_unit]; exact one_ne_zero) : GL (Fin 4) K) ∈ StatedSL 4 K := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    cent2_blk_det_unit]

noncomputable def cent2_card_centralizerElem (ζ : CubeRoot K) (p : Kˣ × GL (Fin 2) K) :
    StatedSL 4 K :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      (cent2_blk (p.1 : K) (((p.1 : K) * (p.2 : Matrix (Fin 2) (Fin 2) K).det)⁻¹)
        (p.2 : Matrix (Fin 2) (Fin 2) K))
      (by rw [cent2_blk_det_unit]; exact one_ne_zero),
    cent2_card_centralizer_det ζ p⟩

theorem cent2_card_centralizerElem_comm (ζ : CubeRoot K) {d : StatedSL 4 K}
    (hd : (d : GL (Fin 4) K) = d₂ ζ) (p : Kˣ × GL (Fin 2) K) :
    cent2_card_centralizerElem ζ p ∈ Subgroup.centralizer ({d} : Set (StatedSL 4 K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, cent1_statedSL_comm_iff, hd]
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, cent2_d₂_eq_diagonal,
    cent2_card_centralizerElem]
  exact cent2_comm_d₂ ζ _ _ _

noncomputable def cent2_card_centralizerMap (ζ : CubeRoot K) {d : StatedSL 4 K}
    (hd : (d : GL (Fin 4) K) = d₂ ζ) :
    Kˣ × GL (Fin 2) K → Subgroup.centralizer ({d} : Set (StatedSL 4 K)) :=
  fun p => ⟨cent2_card_centralizerElem ζ p, cent2_card_centralizerElem_comm ζ hd p⟩

theorem cent2_card_centralizerMap_injective (ζ : CubeRoot K) {d : StatedSL 4 K}
    (hd : (d : GL (Fin 4) K) = d₂ ζ) :
    Function.Injective (cent2_card_centralizerMap ζ hd) := by
  rintro ⟨a, M⟩ ⟨a', M'⟩ hp
  have hgl := congrArg (fun g : Subgroup.centralizer ({d} : Set (StatedSL 4 K)) =>
    ((g : StatedSL 4 K) : GL (Fin 4) K)) hp
  have hgl' := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hgl
  simp only [cent2_card_centralizerMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    cent2_card_centralizerElem] at hgl'
  obtain ⟨ha, hb, hM⟩ := cent2_blk_inj hgl'
  exact Prod.ext (Units.ext ha) (Units.ext hM)

theorem cent2_card_centralizerMap_surjective (ζ : CubeRoot K) {d : StatedSL 4 K}
    (hd : (d : GL (Fin 4) K) = d₂ ζ) :
    Function.Surjective (cent2_card_centralizerMap ζ hd) := by
  rintro ⟨g, hg⟩
  have hcomm : ((g : StatedSL 4 K) : GL (Fin 4) K) * Matrix.diagonal (cent2_A ζ) =
      Matrix.diagonal (cent2_A ζ) * ((g : StatedSL 4 K) : GL (Fin 4) K) := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [cent1_statedSL_comm_iff, hd] at h1
    have h2 := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) h1
    simp only [Units.val_mul] at h2
    rwa [cent2_d₂_eq_diagonal] at h2
  obtain ⟨a, b, M, hgM⟩ := cent2_exists_blk_of_comm ζ hcomm
  have hdet : a * b * M.det = 1 := by
    rw [← cent2_det_blk, ← hgM]
    exact CFSG.Open.StatedAPI.det_of_mem_statedSL (g : StatedSL 4 K).2
  have ha : a ≠ 0 := by
    intro ha0; rw [ha0, zero_mul, zero_mul] at hdet; exact one_ne_zero hdet.symm
  have hM : M.det ≠ 0 := by
    intro hM0; rw [hM0, mul_zero] at hdet; exact one_ne_zero hdet.symm
  have hb : b = (a * M.det)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    linear_combination hdet
  refine ⟨(Units.mk0 a ha, Matrix.GeneralLinearGroup.mkOfDetNeZero M hM), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  dsimp only
  simp only [cent2_card_centralizerMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Units.val_mk0, cent2_card_centralizerElem]
  change cent2_blk a ((a * M.det)⁻¹) M = ((g : StatedSL 4 K) : GL (Fin 4) K)
  rw [show ((a * M.det)⁻¹) = b from hb.symm]
  exact hgM.symm

theorem cent2_card_centralizer (ζ : CubeRoot K) {d : StatedSL 4 K}
    (hd : (d : GL (Fin 4) K) = d₂ ζ) :
    Nat.card (Subgroup.centralizer ({d} : Set (StatedSL 4 K))) =
      Nat.card Kˣ * Nat.card (GL (Fin 2) K) := by
  rw [← Nat.card_prod]
  symm
  exact Nat.card_congr (Equiv.ofBijective (cent2_card_centralizerMap ζ hd)
    ⟨cent2_card_centralizerMap_injective ζ hd, cent2_card_centralizerMap_surjective ζ hd⟩)

theorem cent2_factorization {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    ((r - 1) * (r * ((r - 1) * (r ^ 2 - 1)))).factorization r = 1 := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hA : r - 1 ≠ 0 := by omega
  have hr2 : 1 < r ^ 2 := by nlinarith [hr.two_le]
  have hB2 : r ^ 2 - 1 ≠ 0 := by omega
  have h1 : ¬ r ∣ r - 1 :=
    Nat.not_dvd_of_pos_of_lt (n := r - 1) (m := r) (by omega) (by omega)
  have h2 : ¬ r ∣ r ^ 2 - 1 := by
    intro hdvd
    have hh := Nat.dvd_sub (dvd_mul_right r r) hdvd
    rw [← pow_two] at hh
    rw [Nat.sub_sub_self (show 1 ≤ r ^ 2 by omega)] at hh
    exact hr.not_dvd_one hh
  have hnot : ¬ r ∣ (r - 1) * ((r - 1) * (r ^ 2 - 1)) :=
    hr.not_dvd_mul h1 (hr.not_dvd_mul h1 h2)
  rw [show (r - 1) * (r * ((r - 1) * (r ^ 2 - 1))) =
      r * ((r - 1) * ((r - 1) * (r ^ 2 - 1))) by ac_rfl,
    Nat.factorization_mul hr0 (mul_ne_zero hA (mul_ne_zero hA hB2)),
    Finsupp.add_apply, hr.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]

theorem cent2_card_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) :
    ∀ d : StatedSL 4 K, (d : GL (Fin 4) K) = d₂ ζ →
      (Nat.card (Subgroup.centralizer ({d} : Set (StatedSL 4 K)))).factorization r = 1 := by
  intro d hd
  rw [cent2_card_centralizer ζ hd, Nat.card_units, hK, cent1_card_GL_two hK]
  exact cent2_factorization hr h5

theorem cent3_d3Vec_eq (ζ : CubeRoot K) :
    (fun i : Fin 4 => ζ.pow ((![1, 1, 1, 0] : Fin 4 → ZMod 3) i -
      ∑ j, (![1, 1, 1, 0] : Fin 4 → ZMod 3) j)) =
      (![ζ.ω, ζ.ω, ζ.ω, 1] : Fin 4 → Kˣ) := by
  have hsum : (∑ j : Fin 4, (![1, 1, 1, 0] : Fin 4 → ZMod 3) j) = 0 := by decide
  funext i
  fin_cases i <;>
    first
      | exact cent1_pow_one ζ
      | exact ζ.pow_zero

theorem cent3_coe_d3 (ζ : CubeRoot K) :
    ((d₃ ζ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i => ((![ζ.ω, ζ.ω, ζ.ω, 1] : Fin 4 → Kˣ) i : K)) := by
  have h := cent3_d3Vec_eq ζ
  change Matrix.diagonal (fun i => ((fun i : Fin 4 => ζ.pow
    ((![1, 1, 1, 0] : Fin 4 → ZMod 3) i - ∑ j, (![1, 1, 1, 0] : Fin 4 → ZMod 3) j)) i : K)) =
    Matrix.diagonal (fun i => ((![ζ.ω, ζ.ω, ζ.ω, 1] : Fin 4 → Kˣ) i : K))
  rw [h]

theorem cent3_vec_inl (ζ : CubeRoot K) (i : Fin 3) :
    (![ζ.ω, ζ.ω, ζ.ω, 1] : Fin 4 → Kˣ)
      (finSumFinEquiv (m := 3) (n := 1) (Sum.inl i)) = ζ.ω := by
  fin_cases i <;> simp [show finSumFinEquiv (m := 3) (n := 1) (Sum.inl 0) = (0 : Fin 4) by decide,
    show finSumFinEquiv (m := 3) (n := 1) (Sum.inl 1) = (1 : Fin 4) by decide,
    show finSumFinEquiv (m := 3) (n := 1) (Sum.inl 2) = (2 : Fin 4) by decide]

theorem cent3_vec_inr (ζ : CubeRoot K) (i : Fin 1) :
    (![ζ.ω, ζ.ω, ζ.ω, 1] : Fin 4 → Kˣ)
      (finSumFinEquiv (m := 3) (n := 1) (Sum.inr i)) = 1 := by
  fin_cases i <;> simp [show finSumFinEquiv (m := 3) (n := 1) (Sum.inr 0) = (3 : Fin 4) by decide]

theorem cent3_diagonal_eq_diagBlock {k m : ℕ} (d : Fin (k + m) → K) :
    diagonal d = diagBlock (diagonal fun i => d (finSumFinEquiv (Sum.inl i)))
      (diagonal fun j => d (finSumFinEquiv (Sum.inr j))) := by
  rw [diagBlock, fromBlocks_diagonal, reindex_apply, submatrix_diagonal_equiv]
  congr 1
  funext i
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  rcases a with a | a <;> simp

theorem cent3_diag_eq_diagBlock (ζ : CubeRoot K) :
    Matrix.diagonal (fun i => ((![ζ.ω, ζ.ω, ζ.ω, 1] : Fin 4 → Kˣ) i : K)) =
      diagBlock (Matrix.scalar (Fin 3) (ζ.ω : K)) (Matrix.scalar (Fin 1) (1 : K)) := by
  rw [cent3_diagonal_eq_diagBlock (k := 3) (m := 1)
    (fun i => ((![ζ.ω, ζ.ω, ζ.ω, 1] : Fin 4 → Kˣ) i : K))]
  congr 1
  · rw [show (fun i : Fin 3 => ((![ζ.ω, ζ.ω, ζ.ω, 1] : Fin 4 → Kˣ)
        (finSumFinEquiv (m := 3) (n := 1) (Sum.inl i)) : K)) = fun _ => (ζ.ω : K) by
      funext i
      rw [cent3_vec_inl ζ i]]
    ext i j
    simp [Matrix.scalar_apply]
  · rw [show (fun j : Fin 1 => ((![ζ.ω, ζ.ω, ζ.ω, 1] : Fin 4 → Kˣ)
        (finSumFinEquiv (m := 3) (n := 1) (Sum.inr j)) : K)) = fun _ => (1 : K) by
      funext j
      rw [cent3_vec_inr ζ j]
      simp]
    ext i j
    simp [Matrix.scalar_apply]

@[expose] def cent3_blkMat (A : Matrix (Fin 3) (Fin 3) K) (d : K) : Matrix (Fin 4) (Fin 4) K :=
  diagBlock A (Matrix.scalar (Fin 1) d)

theorem cent3_blkMat_mul (A B : Matrix (Fin 3) (Fin 3) K) (d e : K) :
    cent3_blkMat A d * cent3_blkMat B e = cent3_blkMat (A * B) (d * e) := by
  unfold cent3_blkMat
  rw [diagBlock_mul, ← map_mul]

theorem cent3_blkMat_one : cent3_blkMat (1 : Matrix (Fin 3) (Fin 3) K) 1 = 1 := by
  unfold cent3_blkMat
  rw [show Matrix.scalar (Fin 1) (1 : K) = 1 by simp, diagBlock_one]

theorem cent3_det_diagBlock {k m : ℕ} (A : Matrix (Fin k) (Fin k) K)
    (D : Matrix (Fin m) (Fin m) K) :
    (diagBlock A D).det = A.det * D.det := by
  rw [diagBlock, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

theorem cent3_det_blkMat (A : Matrix (Fin 3) (Fin 3) K) (d : K) :
    (cent3_blkMat A d).det = A.det * d := by
  unfold cent3_blkMat
  rw [cent3_det_diagBlock]
  congr 1
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  simp

@[expose] noncomputable def cent3_blkMon :
    Matrix (Fin 3) (Fin 3) K →* Matrix (Fin 4) (Fin 4) K where
  toFun A := cent3_blkMat A A.det⁻¹
  map_one' := by rw [Matrix.det_one, inv_one, cent3_blkMat_one]
  map_mul' A B := by rw [cent3_blkMat_mul, Matrix.det_mul, mul_inv]

@[expose] noncomputable def cent3_blk : GL (Fin 3) K →* GL (Fin 4) K := Units.map cent3_blkMon

theorem cent3_coe_blk (A : GL (Fin 3) K) :
    ((cent3_blk A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      cent3_blkMat (A : Matrix (Fin 3) (Fin 3) K)
        (A : Matrix (Fin 3) (Fin 3) K).det⁻¹ := rfl

theorem cent3_det_blk (A : GL (Fin 3) K) :
    ((cent3_blk A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [cent3_coe_blk, cent3_det_blkMat, mul_inv_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero A)]

def cent3_ulBlock (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => M (finSumFinEquiv (m := 3) (n := 1) (Sum.inl i))
    (finSumFinEquiv (m := 3) (n := 1) (Sum.inl j))

theorem cent3_ulBlock_blkMat (A : Matrix (Fin 3) (Fin 3) K) (d : K) :
    cent3_ulBlock (cent3_blkMat A d) = A := by
  ext i j
  simp only [cent3_ulBlock, cent3_blkMat, diagBlock, reindex_apply, submatrix_apply,
    Equiv.symm_apply_apply, fromBlocks_apply₁₁]

theorem cent3_blk_injective : Function.Injective (cent3_blk (K := K)) := by
  intro A B h
  apply Units.ext
  have h2 : cent3_ulBlock ((cent3_blk A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      cent3_ulBlock ((cent3_blk B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    congrArg (fun g : Matrix (Fin 4) (Fin 4) K => cent3_ulBlock g)
      (congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) h)
  simpa only [cent3_coe_blk, cent3_ulBlock_blkMat] using h2

theorem cent3_blk_commute_d3 (ζ : CubeRoot K) (A : GL (Fin 3) K) :
    cent3_blk A * d₃ ζ = d₃ ζ * cent3_blk A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, cent3_coe_blk, cent3_coe_d3, cent3_diag_eq_diagBlock]
  unfold cent3_blkMat
  rw [diagBlock_mul, diagBlock_mul, map_one, one_mul, mul_one]
  congr 1
  exact (Matrix.scalar_comm (ζ.ω : K) (fun r => mul_comm _ _)
    (A : Matrix (Fin 3) (Fin 3) K)).symm

theorem cent3_offdiag_zero (ζ : CubeRoot K) (hω : (ζ.ω : K) ≠ 1)
    {M : Matrix (Fin 4) (Fin 4) K}
    (hM : M * diagBlock (k := 3) (m := 1) (Matrix.scalar (Fin 3) (ζ.ω : K)) 1 =
      diagBlock (k := 3) (m := 1) (Matrix.scalar (Fin 3) (ζ.ω : K)) 1 * M) :
    (M.submatrix (finSumFinEquiv (m := 3) (n := 1))
        (finSumFinEquiv (m := 3) (n := 1))).toBlocks₁₂ = 0 ∧
      (M.submatrix (finSumFinEquiv (m := 3) (n := 1))
        (finSumFinEquiv (m := 3) (n := 1))).toBlocks₂₁ = 0 := by
  set M' : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) K :=
    M.submatrix (finSumFinEquiv (m := 3) (n := 1)) (finSumFinEquiv (m := 3) (n := 1))
    with hM'def
  have hM' : M' * fromBlocks (Matrix.scalar (Fin 3) (ζ.ω : K)) 0
        0 (1 : Matrix (Fin 1) (Fin 1) K) =
      fromBlocks (Matrix.scalar (Fin 3) (ζ.ω : K)) 0 0 (1 : Matrix (Fin 1) (Fin 1) K) * M' := by
    have := congrArg (fun A => A.submatrix (finSumFinEquiv (m := 3) (n := 1))
      (finSumFinEquiv (m := 3) (n := 1))) hM
    simp only [diagBlock, reindex_apply] at this
    rw [← submatrix_mul_equiv M _ _ (finSumFinEquiv (m := 3) (n := 1)) _,
      ← submatrix_mul_equiv _ M _ (finSumFinEquiv (m := 3) (n := 1)) _] at this
    simpa only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] using this
  rw [← fromBlocks_toBlocks M', fromBlocks_multiply, fromBlocks_multiply] at hM'
  simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add, Matrix.zero_mul,
    Matrix.one_mul] at hM'
  obtain ⟨-, hB, hC, -⟩ := Matrix.fromBlocks_inj.mp hM'
  have hSB : (Matrix.scalar (Fin 3) (ζ.ω : K)) * M'.toBlocks₁₂ =
      (ζ.ω : K) • M'.toBlocks₁₂ := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul]
  have hCS : M'.toBlocks₂₁ * (Matrix.scalar (Fin 3) (ζ.ω : K)) =
      (ζ.ω : K) • M'.toBlocks₂₁ := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
  have hB0 : M'.toBlocks₁₂ = 0 := by
    have h1 : M'.toBlocks₁₂ = (ζ.ω : K) • M'.toBlocks₁₂ := by rw [← hSB]; exact hB
    have h2 : ((1 : K) - ζ.ω) • M'.toBlocks₁₂ = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hω))
  have hC0 : M'.toBlocks₂₁ = 0 := by
    have h1 : (ζ.ω : K) • M'.toBlocks₂₁ = M'.toBlocks₂₁ := by rw [← hCS]; exact hC
    have h2 : ((ζ.ω : K) - 1) • M'.toBlocks₂₁ = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hω)
  exact ⟨hM'def ▸ hB0, hM'def ▸ hC0⟩

theorem cent3_block_of_comm (ζ : CubeRoot K) (hω : (ζ.ω : K) ≠ 1)
    {M : Matrix (Fin 4) (Fin 4) K}
    (hM : M * diagBlock (k := 3) (m := 1) (Matrix.scalar (Fin 3) (ζ.ω : K)) 1 =
      diagBlock (k := 3) (m := 1) (Matrix.scalar (Fin 3) (ζ.ω : K)) 1 * M) :
    ∃ A D, M = diagBlock (k := 3) (m := 1) A D := by
  obtain ⟨hB0, hC0⟩ := cent3_offdiag_zero ζ hω hM
  have hMM : M = reindex (finSumFinEquiv (m := 3) (n := 1))
      (finSumFinEquiv (m := 3) (n := 1))
      (M.submatrix (finSumFinEquiv (m := 3) (n := 1)) (finSumFinEquiv (m := 3) (n := 1))) := by
    ext a b
    simp
  have hM'' : (M.submatrix (finSumFinEquiv (m := 3) (n := 1))
      (finSumFinEquiv (m := 3) (n := 1))) =
      fromBlocks (M.submatrix (finSumFinEquiv (m := 3) (n := 1))
        (finSumFinEquiv (m := 3) (n := 1))).toBlocks₁₁ 0 0
        (M.submatrix (finSumFinEquiv (m := 3) (n := 1))
          (finSumFinEquiv (m := 3) (n := 1))).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (M.submatrix (finSumFinEquiv (m := 3) (n := 1))
      (finSumFinEquiv (m := 3) (n := 1)))]
    rw [hB0, hC0]
  rw [hMM, hM'']
  exact ⟨_, _, rfl⟩

theorem cent3_exists_blk_of_commute (ζ : CubeRoot K) (hω : (ζ.ω : K) ≠ 1)
    {y : GL (Fin 4) K} (hy : y * d₃ ζ = d₃ ζ * y)
    (hdet : ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1) :
    ∃ A : GL (Fin 3) K, cent3_blk A = y := by
  have hyM : (y : Matrix (Fin 4) (Fin 4) K) *
        diagBlock (k := 3) (m := 1) (Matrix.scalar (Fin 3) (ζ.ω : K)) 1 =
      diagBlock (k := 3) (m := 1) (Matrix.scalar (Fin 3) (ζ.ω : K)) 1 *
        (y : Matrix (Fin 4) (Fin 4) K) := by
    have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hy
    simpa [Units.val_mul, cent3_coe_d3, cent3_diag_eq_diagBlock, map_one] using this
  obtain ⟨A, D, hAD⟩ := cent3_block_of_comm ζ hω hyM
  have hdetAD : A.det * D.det = 1 := by
    rw [← cent3_det_diagBlock, ← hAD, hdet]
  have hD00 : D = Matrix.scalar (Fin 1) (D 0 0) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  have hdetD : D.det = D 0 0 := by
    rw [hD00, Matrix.scalar_apply, Matrix.det_diagonal]
    simp
  have hD : D = Matrix.scalar (Fin 1) (A.det)⁻¹ := by
    rw [hD00]
    congr 1
    rw [hdetD] at hdetAD
    exact eq_inv_of_mul_eq_one_right hdetAD
  have hAne : A.det ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hdetAD
    exact zero_ne_one hdetAD
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAne, ?_⟩
  apply Units.ext
  rw [cent3_coe_blk, hAD, hD]
  rfl

theorem cent3_hω (ζ : CubeRoot K) : (ζ.ω : K) ≠ 1 := fun h => ζ.ne_one (Units.ext h)

@[expose] def cent3_x (ζ : CubeRoot K) : StatedSL 4 K :=
  ⟨d₃ ζ, mem_statedSL_of_det
    (det_stdDiagHom ζ (Multiplicative.ofAdd ![1, 1, 1, 0]))⟩

noncomputable def cent3_phiHom (ζ : CubeRoot K) : GL (Fin 3) K →* StatedSL 4 K where
  toFun A := ⟨cent3_blk A, mem_statedSL_of_det (cent3_det_blk A)⟩
  map_one' := Subtype.ext (map_one cent3_blk)
  map_mul' A B := Subtype.ext (map_mul cent3_blk A B)

theorem cent3_phiHom_injective (ζ : CubeRoot K) :
    Function.Injective (cent3_phiHom ζ) := fun A B h =>
  cent3_blk_injective (K := K) (congrArg (fun g : StatedSL 4 K => (g : GL (Fin 4) K)) h)

theorem cent3_phiHom_range (ζ : CubeRoot K) :
    (cent3_phiHom ζ).range =
      Subgroup.centralizer ({cent3_x ζ} : Set (StatedSL 4 K)) := by
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (cent3_blk A : GL (Fin 4) K) * d₃ ζ = d₃ ζ * cent3_blk A
    exact cent3_blk_commute_d3 ζ A
  · intro hg
    have hgcomm : (g : GL (Fin 4) K) * d₃ ζ = d₃ ζ * (g : GL (Fin 4) K) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hg
      simpa [cent3_x] using congrArg (fun x : StatedSL 4 K => (x : GL (Fin 4) K)) this
    have hgdet : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 :=
      det_of_mem_statedSL g.2
    obtain ⟨A, hA⟩ := cent3_exists_blk_of_commute ζ (cent3_hω ζ) hgcomm hgdet
    exact ⟨A, Subtype.ext hA⟩

theorem cent3_card_centralizer (ζ : CubeRoot K) :
    Nat.card (Subgroup.centralizer ({cent3_x ζ} : Set (StatedSL 4 K))) =
      Nat.card (GL (Fin 3) K) := by
  rw [← cent3_phiHom_range ζ]
  exact Nat.card_range_of_injective (cent3_phiHom_injective ζ)

theorem cent3_factorization_GL3 {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    (Nat.card (GL (Fin 3) K)).factorization r = 3 := by
  rw [card_GL_eq 3, hK, show 3 * (3 - 1) / 2 = 3 by norm_num]
  rw [prod_Icc_one_eq (fun j => r ^ j - 1) (n := 3) (by norm_num)]
  have hpq : r ∣ Nat.card K := by rw [hK]
  have hnot : ¬ r ∣ (r ^ 1 - 1) * (∏ j ∈ Finset.Icc 2 3, (r ^ j - 1)) := by
    rw [Nat.Prime.dvd_mul hr]
    rintro (h | h)
    · rw [pow_one] at h
      have hlt : r - 1 < r := Nat.sub_lt hr.pos one_pos
      have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hr.one_lt) h
      omega
    · exact not_dvd_prod_pow_sub_one hr (dvd_refl r) hr.one_le 3 h
  have hMne : (r ^ 1 - 1) * (∏ j ∈ Finset.Icc 2 3, (r ^ j - 1)) ≠ 0 := by
    have h1 : r ^ 1 - 1 ≠ 0 := by
      rw [pow_one]
      exact ne_of_gt (Nat.sub_pos_of_lt hr.one_lt)
    refine mul_ne_zero h1 (Finset.prod_ne_zero_iff.mpr ?_)
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact ne_of_gt (Nat.sub_pos_of_lt (one_lt_pow' hr.one_lt (by omega)))
  rw [Nat.factorization_mul (pow_ne_zero 3 hr.ne_zero) hMne, hr.factorization_pow,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]
  simp

theorem cent3_card_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) :
    ∀ d : StatedSL 4 K, (d : GL (Fin 4) K) = d₃ ζ →
      (Nat.card (Subgroup.centralizer ({d} : Set (StatedSL 4 K)))).factorization r = 3 := by
  intro d hd
  have hdx : d = cent3_x ζ := Subtype.ext hd
  rw [hdx, cent3_card_centralizer]
  exact cent3_factorization_GL3 hr hK

theorem cent3_pRank_le_two_of_sylow_nonab {r : ℕ} (hr : r.Prime) {S : Type} [Group S]
    [Finite S] (U : Subgroup S) (hU : IsPGroup r U) (hidx : ¬ r ∣ U.index)
    (hcard : Nat.card U = r ^ 3) (hnonab : ∃ u ∈ U, ∃ v ∈ U, u * v ≠ v * u) :
    pRank r (⊤ : Subgroup S) ≤ 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  rw [← (CFSG.SectionRank.pRank_sylow (hU.toSylow hidx)).1, IsPGroup.toSylow_coe hU hidx]
  refine CFSG.SectionRank.pRank_le hr.one_lt fun E hE hEa => ?_
  have hEpg : IsPGroup r ↥E := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one, orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (hEa.2 (x : S) x.2)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hEpg
  have hmle : m ≤ 3 := by
    have h1 : r ^ m ≤ r ^ 3 := by rw [← hm, ← hcard]; exact Subgroup.card_le_of_le hE
    exact (Nat.pow_le_pow_iff_right hr.one_lt).1 h1
  by_cases hm3 : m = 3
  · exfalso
    have hEU : E = U := Subgroup.eq_of_le_of_card_ge hE (by rw [hm, hm3, hcard])
    obtain ⟨u, hu, v, hv, huv⟩ := hnonab
    have hcomm : IsMulCommutative ↥U := hEU ▸ hEa.1
    exact huv (congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : U) (⟨v, hv⟩ : U)))
  · have hm2 : m ≤ 2 := by omega
    rw [hm]
    exact Nat.pow_le_pow_right hr.pos hm2

theorem cent3_det_transvection01 :
    (Matrix.transvection (0 : Fin 3) (1 : Fin 3) (1 : K)).det = 1 :=
  Matrix.det_transvection_of_ne (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) (1 : K)

theorem cent3_det_transvection12 :
    (Matrix.transvection (1 : Fin 3) (2 : Fin 3) (1 : K)).det = 1 :=
  Matrix.det_transvection_of_ne (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) (1 : K)

theorem cent3_det_transvection02 :
    (Matrix.transvection (0 : Fin 3) (2 : Fin 3) (1 : K)).det = 1 :=
  Matrix.det_transvection_of_ne (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) (1 : K)

@[expose] def cent3_s01 : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection (0 : Fin 3) (1 : Fin 3) (1 : K), cent3_det_transvection01⟩

@[expose] def cent3_s12 : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection (1 : Fin 3) (2 : Fin 3) (1 : K), cent3_det_transvection12⟩

@[expose] def cent3_s02 : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection (0 : Fin 3) (2 : Fin 3) (1 : K), cent3_det_transvection02⟩

@[expose] def cent3_t01 : GL (Fin 3) K := SpecialLinearGroup.toGL (cent3_s01 (K := K))

@[expose] def cent3_t12 : GL (Fin 3) K := SpecialLinearGroup.toGL (cent3_s12 (K := K))

@[expose] def cent3_t02 : GL (Fin 3) K := SpecialLinearGroup.toGL (cent3_s02 (K := K))

theorem cent3_t01_val : ((cent3_t01 (K := K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.transvection (0 : Fin 3) (1 : Fin 3) (1 : K) := rfl

theorem cent3_t12_val : ((cent3_t12 (K := K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.transvection (1 : Fin 3) (2 : Fin 3) (1 : K) := rfl

theorem cent3_t02_val : ((cent3_t02 (K := K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.transvection (0 : Fin 3) (2 : Fin 3) (1 : K) := rfl

theorem cent3_t01_pow_val (m : ℕ) :
    (((cent3_t01 (K := K)) ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection (0 : Fin 3) (1 : Fin 3) (m • (1 : K)) := by
  rw [Units.val_pow_eq_pow_val, cent3_t01_val]
  exact cent1_transvection_pow (n := Fin 3) (0 : Fin 3) 1 (by decide) 1 m

theorem cent3_t02_pow_val (m : ℕ) :
    (((cent3_t02 (K := K)) ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection (0 : Fin 3) (2 : Fin 3) (m • (1 : K)) := by
  rw [Units.val_pow_eq_pow_val, cent3_t02_val]
  exact cent1_transvection_pow (n := Fin 3) (0 : Fin 3) 2 (by decide) 1 m

theorem cent3_t01_pow_r {r : ℕ} (hK : Nat.card K = r) : (cent3_t01 (K := K)) ^ r = 1 := by
  apply Units.ext
  rw [cent3_t01_pow_val, cent1_nsmul_one_eq_zero (K := K) hK, Matrix.transvection_zero,
    Units.val_one]

theorem cent3_t02_pow_r {r : ℕ} (hK : Nat.card K = r) : (cent3_t02 (K := K)) ^ r = 1 := by
  apply Units.ext
  rw [cent3_t02_pow_val, cent1_nsmul_one_eq_zero (K := K) hK, Matrix.transvection_zero,
    Units.val_one]

theorem cent3_t01_ne_one : (cent3_t01 (K := K)) ≠ 1 := by
  intro h
  have hh := congrArg (fun u : GL (Fin 3) K =>
    (u : Matrix (Fin 3) (Fin 3) K) (0 : Fin 3) (1 : Fin 3)) h
  rw [cent3_t01_val] at hh
  simpa [Matrix.transvection, Matrix.single_apply] using hh

theorem cent3_t02_ne_one : (cent3_t02 (K := K)) ≠ 1 := by
  intro h
  have hh := congrArg (fun u : GL (Fin 3) K =>
    (u : Matrix (Fin 3) (Fin 3) K) (0 : Fin 3) (2 : Fin 3)) h
  rw [cent3_t02_val] at hh
  simpa [Matrix.transvection, Matrix.single_apply] using hh

theorem cent3_orderOf_t01 {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    orderOf (cent3_t01 (K := K)) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  exact orderOf_eq_prime (cent3_t01_pow_r hK) cent3_t01_ne_one

theorem cent3_orderOf_t02 {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    orderOf (cent3_t02 (K := K)) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  exact orderOf_eq_prime (cent3_t02_pow_r hK) cent3_t02_ne_one

theorem cent3_t01_commute_t02 :
    Commute (cent3_t01 (K := K)) (cent3_t02 (K := K)) := by
  rw [Commute]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, cent3_t01_val, cent3_t02_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three]

theorem cent3_t12_mul_t01_apply :
    (Matrix.transvection (1 : Fin 3) (2 : Fin 3) (1 : K) *
      Matrix.transvection (0 : Fin 3) (1 : Fin 3) (1 : K)) 0 2 = 0 := by
  simp [Matrix.transvection, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three]

theorem cent3_t01_mul_t12_apply :
    (Matrix.transvection (0 : Fin 3) (1 : Fin 3) (1 : K) *
      Matrix.transvection (1 : Fin 3) (2 : Fin 3) (1 : K)) 0 2 = 1 := by
  simp [Matrix.transvection, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three]

theorem cent3_t12_not_commute_t01 :
    ¬ Commute (cent3_t12 (K := K)) (cent3_t01 (K := K)) := by
  intro h
  have hh := congrFun (congrFun (congrArg (fun u : GL (Fin 3) K =>
    (u : Matrix (Fin 3) (Fin 3) K)) h) 0) 2
  rw [Units.val_mul, Units.val_mul, cent3_t01_val, cent3_t12_val] at hh
  rw [cent3_t12_mul_t01_apply, cent3_t01_mul_t12_apply] at hh
  exact zero_ne_one hh

theorem cent3_t01_zpow_apply {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) (n : ℤ) :
    (((cent3_t01 (K := K)) ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
  have hper : (cent3_t01 (K := K)) ^ (r : ℤ) = 1 := by
    rw [zpow_natCast]
    exact cent3_t01_pow_r hK
  rw [zpow_eq_zpow_emod n hper]
  have hnn : 0 ≤ n % (r : ℤ) := Int.emod_nonneg n (by exact_mod_cast hr.ne_zero)
  rw [← Int.toNat_of_nonneg hnn, zpow_natCast, cent3_t01_pow_val]
  simp [Matrix.transvection, Matrix.single_apply]

theorem cent3_t02_not_mem_zpowers_t01 {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    (cent3_t02 (K := K)) ∉ Subgroup.zpowers (cent3_t01 (K := K)) := by
  intro h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  have h1 : (((cent3_t01 (K := K)) ^ n : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := cent3_t01_zpow_apply hr hK n
  rw [hn, cent3_t02_val] at h1
  simpa [Matrix.transvection, Matrix.single_apply] using h1

noncomputable def cent3_unitriangularGL : Subgroup (GL (Fin 3) K) :=
  (unitriangular 3 K).map SpecialLinearGroup.toGL

theorem cent3_card_unitriangularGL :
    Nat.card (cent3_unitriangularGL (K := K)) = Nat.card K ^ 3 := by
  rw [cent3_unitriangularGL, Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective,
    card_unitriangular]

theorem cent3_index_unitriangularGL {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    (cent3_unitriangularGL (K := K)).index = (r - 1) * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
  have hcard : Nat.card (cent3_unitriangularGL (K := K)) = r ^ 3 := by
    rw [cent3_card_unitriangularGL, hK]
  have hprod : (∏ j ∈ Finset.Icc 1 3, (r ^ j - 1)) =
      (r - 1) * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
    rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]
    simp
  have hGL : Nat.card (GL (Fin 3) K) = r ^ 3 * ((r - 1) * ((r ^ 2 - 1) * (r ^ 3 - 1))) := by
    rw [card_GL_eq 3, hK]
    rw [show 3 * (3 - 1) / 2 = 3 by norm_num, hprod]
  have h := (cent3_unitriangularGL (K := K)).card_mul_index
  rw [hcard, hGL] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hr.pos 3) h

theorem cent3_not_dvd_index_unitriangularGL {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    ¬ r ∣ (cent3_unitriangularGL (K := K)).index := by
  rw [cent3_index_unitriangularGL hr hK]
  have hpq : r ∣ Nat.card K := by rw [hK]
  have hM : ¬ r ∣ (r - 1) * (∏ j ∈ Finset.Icc 2 3, (r ^ j - 1)) := by
    rw [Nat.Prime.dvd_mul hr]
    rintro (h | h)
    · have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hr.one_lt) h
      have hlt : r - 1 < r := Nat.sub_lt hr.pos one_pos
      omega
    · exact not_dvd_prod_pow_sub_one hr (dvd_refl r) hr.one_le 3 h
  convert hM using 2
  rw [show Finset.Icc 2 3 = {2, 3} by decide]
  simp

theorem cent3_mem_unitriangularGL01 :
    cent3_t01 (K := K) ∈ cent3_unitriangularGL (K := K) := by
  refine Subgroup.mem_map_of_mem _ (mem_unitriangular.mpr ⟨?_, ?_⟩)
  · intro i j hij
    rw [show (cent3_s01 (K := K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection (0 : Fin 3) (1 : Fin 3) (1 : K) from rfl]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | simp [Matrix.transvection, Matrix.single_apply]
  · intro i
    rw [show (cent3_s01 (K := K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection (0 : Fin 3) (1 : Fin 3) (1 : K) from rfl]
    fin_cases i <;> simp [Matrix.transvection, Matrix.single_apply]

theorem cent3_mem_unitriangularGL12 :
    cent3_t12 (K := K) ∈ cent3_unitriangularGL (K := K) := by
  refine Subgroup.mem_map_of_mem _ (mem_unitriangular.mpr ⟨?_, ?_⟩)
  · intro i j hij
    rw [show (cent3_s12 (K := K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection (1 : Fin 3) (2 : Fin 3) (1 : K) from rfl]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | simp [Matrix.transvection, Matrix.single_apply]
  · intro i
    rw [show (cent3_s12 (K := K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection (1 : Fin 3) (2 : Fin 3) (1 : K) from rfl]
    fin_cases i <;> simp [Matrix.transvection, Matrix.single_apply]

theorem cent3_nonab_unitriangularGL :
    ∃ u ∈ cent3_unitriangularGL (K := K), ∃ v ∈ cent3_unitriangularGL (K := K),
      u * v ≠ v * u :=
  ⟨cent3_t01, cent3_mem_unitriangularGL01, cent3_t12, cent3_mem_unitriangularGL12,
    fun h => cent3_t12_not_commute_t01 h.symm⟩

theorem cent3_pRank_GL3_le {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    pRank r (⊤ : Subgroup (GL (Fin 3) K)) ≤ 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  exact cent3_pRank_le_two_of_sylow_nonab hr (cent3_unitriangularGL (K := K))
    (IsPGroup.of_card (n := 3) (by rw [cent3_card_unitriangularGL, hK]))
    (cent3_not_dvd_index_unitriangularGL hr hK)
    (by rw [cent3_card_unitriangularGL, hK]) cent3_nonab_unitriangularGL

theorem cent3_pRank_GL3_ge {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    2 ≤ pRank r (⊤ : Subgroup (GL (Fin 3) K)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  exact CFSG.GroupTheory.two_le_pRank_of_commute (H := ⊤)
    (Subgroup.mem_top _) (Subgroup.mem_top _)
    (cent3_orderOf_t01 hr hK) (cent3_orderOf_t02 hr hK)
    (cent3_t01_commute_t02 (K := K)) (cent3_t02_not_mem_zpowers_t01 hr hK)

theorem cent3_pRank_GL3 {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r) :
    pRank r (⊤ : Subgroup (GL (Fin 3) K)) = 2 :=
  le_antisymm (cent3_pRank_GL3_le hr hK) (cent3_pRank_GL3_ge hr hK)

theorem cent3_pRank_centralizer {r : ℕ} (hr : r.Prime) (ζ : CubeRoot K) :
    pRank r (Subgroup.centralizer ({cent3_x ζ} : Set (StatedSL 4 K))) =
      pRank r (⊤ : Subgroup (GL (Fin 3) K)) := by
  have h1 : pRank r (Subgroup.centralizer ({cent3_x ζ} : Set (StatedSL 4 K))) =
      pRank r (⊤ : Subgroup ((cent3_phiHom ζ).range)) := by
    rw [← cent3_phiHom_range ζ,
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup ((cent3_phiHom ζ).range)]
  rw [h1]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
    (MonoidHom.ofInjective (cent3_phiHom_injective ζ))).symm

theorem cent3_rank_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r)
    (ζ : CubeRoot K) :
    ∀ d : StatedSL 4 K, (d : GL (Fin 4) K) = d₃ ζ →
      pRank r (Subgroup.centralizer ({d} : Set (StatedSL 4 K))) = 2 := by
  intro d hd
  have hdx : d = cent3_x ζ := Subtype.ext hd
  rw [hdx, cent3_pRank_centralizer hr ζ, cent3_pRank_GL3 hr hK]

theorem cent4_det_diagUnit (u : Fin 4 → Kˣ) :
    ((diagUnit u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = ∏ i, (u i : K) := by
  simp [diagUnit, Matrix.det_diagonal]

theorem cent4_diagUnit_injective : Function.Injective (diagUnit (K := K)) := by
  intro u v h
  have hd := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) h
  have hd' := Matrix.diagonal_injective (by simpa [diagUnit] using hd)
  funext i
  exact Units.ext (by simpa using congrFun hd' i)

@[expose] def cent4_torusVec : (Kˣ × Kˣ × Kˣ) →* (Fin 4 → Kˣ) where
  toFun p := ![p.1, p.2.1, p.2.2, (p.1 * p.2.1 * p.2.2)⁻¹]
  map_one' := by
    ext i
    fin_cases i <;> simp
  map_mul' p q := by
    ext i
    fin_cases i <;> simp [Pi.mul_apply, mul_inv] <;> ring

theorem cent4_torusVec_injective : Function.Injective (cent4_torusVec (K := K)) := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [cent4_torusVec] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

@[expose] noncomputable def cent4_torusHom : (Kˣ × Kˣ × Kˣ) →* GL (Fin 4) K where
  toFun p := diagUnit (cent4_torusVec p)
  map_one' := by rw [map_one, diagUnit_one]
  map_mul' p q := by rw [map_mul, diagUnit_mul]

theorem cent4_torusHom_injective : Function.Injective (cent4_torusHom (K := K)) :=
  (cent4_diagUnit_injective (K := K)).comp (cent4_torusVec_injective (K := K))

theorem cent4_det_torusHom (p : Kˣ × Kˣ × Kˣ) :
    ((cent4_torusHom (K := K) p : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [show cent4_torusHom (K := K) p = diagUnit (cent4_torusVec p) from rfl,
    cent4_det_diagUnit]
  change (∏ i, ((![p.1, p.2.1, p.2.2,
    (p.1 * p.2.1 * p.2.2)⁻¹] : Fin 4 → Kˣ) i : K)) = 1
  rw [Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_mul]
  field_simp

@[expose] noncomputable def cent4_torusHomSL : (Kˣ × Kˣ × Kˣ) →* StatedSL 4 K where
  toFun p := ⟨cent4_torusHom p, mem_statedSL_of_det (cent4_det_torusHom p)⟩
  map_one' := Subtype.ext (map_one (cent4_torusHom (K := K)))
  map_mul' p q := Subtype.ext (map_mul (cent4_torusHom (K := K)) p q)

theorem cent4_torusHomSL_injective : Function.Injective (cent4_torusHomSL (K := K)) := by
  intro p q h
  exact cent4_torusHom_injective (congrArg (fun g : StatedSL 4 K => (g : GL (Fin 4) K)) h)

theorem cent4_torus_mem_centralizer (ζ : CubeRoot K) (p : Kˣ × Kˣ × Kˣ) :
    cent4_torusHomSL p ∈ Subgroup.centralizer
      (((D₀ ζ).subgroupOf (StatedSL 4 K) : Subgroup (StatedSL 4 K)) :
        Set (StatedSL 4 K)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhD : (h : GL (Fin 4) K) ∈ D₀ ζ := hh
  obtain ⟨v, hv⟩ : (h : GL (Fin 4) K) ∈ (stdDiagHom ζ).range := by
    simpa [D₀] using hhD
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  change (h : GL (Fin 4) K) * (cent4_torusHom p : GL (Fin 4) K) =
    (cent4_torusHom p : GL (Fin 4) K) * (h : GL (Fin 4) K)
  rw [← hv]
  change diagUnit (fun i => ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j)) *
      diagUnit (cent4_torusVec p) =
    diagUnit (cent4_torusVec p) *
      diagUnit (fun i => ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j))
  rw [← diagUnit_mul, ← diagUnit_mul]
  congr 1
  exact mul_comm _ _

@[expose] noncomputable def cent4_torusSub (ζ : CubeRoot K) : Subgroup (StatedSL 4 K) :=
  (cent4_torusHomSL (K := K)).range

theorem cent4_torusSub_le (ζ : CubeRoot K) :
    cent4_torusSub ζ ≤ Subgroup.centralizer
      (((D₀ ζ).subgroupOf (StatedSL 4 K) : Subgroup (StatedSL 4 K)) :
        Set (StatedSL 4 K)) := by
  rintro g ⟨p, rfl⟩
  exact cent4_torus_mem_centralizer ζ p

theorem cent4_card_torusSub {r : ℕ} (hK : Nat.card K = r) (ζ : CubeRoot K) :
    Nat.card (cent4_torusSub ζ) = (r - 1) ^ 3 := by
  have hcard : Nat.card (cent4_torusSub ζ) = Nat.card (Kˣ × Kˣ × Kˣ) := by
    rw [cent4_torusSub]
    exact (Nat.card_congr
      (MonoidHom.ofInjective (cent4_torusHomSL_injective (K := K))).toEquiv).symm
  rw [hcard, Nat.card_prod, Nat.card_prod, Nat.card_units, hK]
  ring

theorem cent4_factorization_torus {r : ℕ} (hr : r.Prime) :
    ((r - 1) ^ 3).factorization 3 = 3 * ((r - 1).factorization 3) := by
  rw [Nat.factorization_pow]
  simp [nsmul_eq_mul]

theorem cent4_factorization_d2 {r : ℕ} (hr : r.Prime) (h3 : r % 3 = 1) :
    ((r - 1) * (r * ((r - 1) * (r ^ 2 - 1)))).factorization 3 =
      3 * ((r - 1).factorization 3) := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hr2 : 2 ≤ r := hr.two_le
  have hA : r - 1 ≠ 0 := by omega
  have hB : r ^ 2 - 1 ≠ 0 := by
    have hlt : 1 < r ^ 2 := one_lt_pow' hr.one_lt (by norm_num)
    exact (Nat.sub_ne_zero_iff_lt (n := r ^ 2) (m := 1)).mpr hlt
  have hsq : r ^ 2 - 1 = (r - 1) * (r + 1) := by
    have h1 : 1 ≤ r := hr.one_le
    have h2 : 1 ≤ r ^ 2 := by nlinarith [hr.two_le]
    zify [h1, h2]
    ring
  have hr3 : ¬ 3 ∣ r := by
    intro h
    have := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  have hr13 : ¬ 3 ∣ r + 1 := by
    intro h
    have := Nat.dvd_iff_mod_eq_zero.mp h
    rw [Nat.add_mod, h3] at this
    omega
  have hsqfac : (r ^ 2 - 1).factorization 3 = (r - 1).factorization 3 := by
    rw [hsq, Nat.factorization_mul hA (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hr13, add_zero]
  rw [show (r - 1) * (r * ((r - 1) * (r ^ 2 - 1))) =
      r * ((r - 1) * ((r - 1) * (r ^ 2 - 1))) by ac_rfl,
    Nat.factorization_mul hr0 (mul_ne_zero hA (mul_ne_zero hA hB)), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hr3, zero_add,
    Nat.factorization_mul hA (mul_ne_zero hA hB), Finsupp.add_apply,
    Nat.factorization_mul hA hB, Finsupp.add_apply, hsqfac]
  ring_nf

theorem cent4_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r) (h3 : r % 3 = 1)
    (ζ : CubeRoot K) :
    ∀ d : StatedSL 4 K, (d : GL (Fin 4) K) = d₂ ζ →
      (Nat.card (Subgroup.centralizer
        (((D₀ ζ).subgroupOf (StatedSL 4 K) : Subgroup (StatedSL 4 K)) :
          Set (StatedSL 4 K)))).factorization 3 =
        (Nat.card (Subgroup.centralizer ({d} : Set (StatedSL 4 K)))).factorization 3 := by
  intro d hd
  set C0 := Subgroup.centralizer (((D₀ ζ).subgroupOf (StatedSL 4 K) :
    Subgroup (StatedSL 4 K)) : Set (StatedSL 4 K)) with hC0
  set C1 := Subgroup.centralizer ({d} : Set (StatedSL 4 K)) with hC1
  have hd_mem : d ∈ (D₀ ζ).subgroupOf (StatedSL 4 K) := by
    show (d : GL (Fin 4) K) ∈ D₀ ζ
    rw [hd]
    exact ⟨Multiplicative.ofAdd ![1, -1, 0, 0], rfl⟩
  have hsub : ({d} : Set (StatedSL 4 K)) ⊆
      ((D₀ ζ).subgroupOf (StatedSL 4 K) : Set (StatedSL 4 K)) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rwa [hx]
  have hle : C0 ≤ C1 := Subgroup.centralizer_le hsub
  have hdvd : Nat.card C0 ∣ Nat.card C1 := Subgroup.card_dvd_of_le hle
  have hfac_le : (Nat.card C0).factorization 3 ≤ (Nat.card C1).factorization 3 :=
    ((Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr hdvd) 3
  have hC1fac : (Nat.card C1).factorization 3 = 3 * ((r - 1).factorization 3) := by
    rw [hC1, cent2_card_centralizer ζ hd, Nat.card_units, hK, cent1_card_GL_two hK]
    exact cent4_factorization_d2 hr h3
  have hT : Nat.card (cent4_torusSub ζ) = (r - 1) ^ 3 := cent4_card_torusSub hK ζ
  have hdvdT : Nat.card (cent4_torusSub ζ) ∣ Nat.card C0 := by
    apply Subgroup.card_dvd_of_le
    rw [hC0]
    exact cent4_torusSub_le ζ
  have hfac_ge : 3 * ((r - 1).factorization 3) ≤ (Nat.card C0).factorization 3 := by
    rw [← cent4_factorization_torus hr, ← hT]
    exact ((Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr hdvdT) 3
  have h2 : (Nat.card C1).factorization 3 ≤ (Nat.card C0).factorization 3 := by
    rw [hC1fac]
    exact hfac_ge
  exact le_antisymm hfac_le h2

theorem centFact_sl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r) (h3 : r % 3 = 1)
    (ζ : CubeRoot K) : CentFact (StatedSL 4 K) ζ r :=
  ⟨fun d hd => ⟨cent1_card_sl hr h5 hK ζ d hd, cent1_rank_sl hr h5 hK ζ d hd⟩,
    cent2_card_sl hr h5 hK ζ,
    fun d hd => ⟨cent3_card_sl hr h5 hK ζ d hd, cent3_rank_sl hr h5 hK ζ d hd⟩,
    cent4_sl hr h5 hK h3 ζ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
