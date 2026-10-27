module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusModel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusExt
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamAct
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRankOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open Matrix
open scoped MatrixGroups

@[expose] noncomputable def plusRootEmbTwo (K : Type) [Field K] : SL(2, K) →* PlusLin K :=
  (plusResExt K (show 1 + 2 = 3 from rfl)).comp (plusIotaTwo K)

@[expose] def plusDiagSL2 {K : Type} [Field K] (b : Kˣ) : SL(2, K) :=
  ⟨Matrix.diagonal ![(b : K), ((b⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

private def plusDiagSL2Hom_E05 (K : Type) [Field K] : Kˣ →* SL(2, K) where
  toFun := plusDiagSL2
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [plusDiagSL2]
  map_mul' a b := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [plusDiagSL2, Matrix.diagonal_mul_diagonal, Units.val_mul,
        Units.val_inv_eq_inv_val, _root_.mul_inv_rev, mul_comm]

private theorem plusDiagSL2_injective_E05 {K : Type} [Field K] :
    Function.Injective (plusDiagSL2 (K := K)) := by
  intro a b h
  apply Units.ext
  simpa [plusDiagSL2] using
    congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h

private theorem autMat_inv_torusElt_E05 {r : ℕ} {K : Type} [Field K] (a : Fin r → Kˣ) :
    autMat ((torusElt r K a)⁻¹) =
      Matrix.diagonal (fun x => (((Sum.elim a a⁻¹ x)⁻¹ : Kˣ) : K)) := by
  rw [← map_inv (torusElt r K) a, autMat_torusElt]
  congr 1
  funext x
  rcases x with i | i <;> simp

private theorem diag_mul_extendMat_mul_diag_E05 {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {K : Type*} [Field K] {φ : ι → κ}
    (hφ : Function.Injective φ) (d : κ → Kˣ) (B : Matrix ι ι K) :
    Matrix.diagonal (fun x => (d x : K)) * extendMat hφ B *
        Matrix.diagonal (fun x => (((d x)⁻¹ : Kˣ) : K)) =
      extendMat hφ (Matrix.diagonal (fun i => (d (φ i) : K)) * B *
        Matrix.diagonal (fun i => (((d (φ i))⁻¹ : Kˣ) : K))) := by
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hx : x ∈ Set.range φ
  · obtain ⟨i, rfl⟩ := hx
    by_cases hy : y ∈ Set.range φ
    · obtain ⟨j, rfl⟩ := hy
      rw [extendMat_apply_map (hφ := hφ) (B := B) (i := i) (j := j),
        extendMat_apply_map (hφ := hφ)
          (B := Matrix.diagonal (fun k => (d (φ k) : K)) * B *
            Matrix.diagonal (fun k => (((d (φ k))⁻¹ : Kˣ) : K))) (i := i) (j := j)]
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    · rw [extendMat_apply_of_not_mem (hφ := hφ) (B := B) (x := φ i) (y := y) (Or.inr hy),
        extendMat_apply_of_not_mem (hφ := hφ)
          (B := Matrix.diagonal (fun k => (d (φ k) : K)) * B *
            Matrix.diagonal (fun k => (((d (φ k))⁻¹ : Kˣ) : K)))
          (x := φ i) (y := y) (Or.inr hy),
        Matrix.one_apply_ne (i := φ i) (j := y) (fun h => hy ⟨i, h⟩), mul_zero, zero_mul]
  · by_cases hy : y ∈ Set.range φ
    · obtain ⟨j, rfl⟩ := hy
      rw [extendMat_apply_of_not_mem (hφ := hφ) (B := B) (x := x) (y := φ j) (Or.inl hx),
        extendMat_apply_of_not_mem (hφ := hφ)
          (B := Matrix.diagonal (fun k => (d (φ k) : K)) * B *
            Matrix.diagonal (fun k => (((d (φ k))⁻¹ : Kˣ) : K)))
          (x := x) (y := φ j) (Or.inl hx),
        Matrix.one_apply_ne (i := x) (j := φ j) (fun h => hx ⟨j, h.symm⟩), mul_zero, zero_mul]
    · by_cases hxy : x = y
      · subst hxy
        rw [extendMat_apply_of_not_mem (hφ := hφ) (B := B) (x := x) (y := x) (Or.inl hx),
          extendMat_apply_of_not_mem (hφ := hφ)
            (B := Matrix.diagonal (fun k => (d (φ k) : K)) * B *
              Matrix.diagonal (fun k => (((d (φ k))⁻¹ : Kˣ) : K)))
            (x := x) (y := x) (Or.inl hx),
          Matrix.one_apply_eq, mul_one]
        exact Units.mul_inv (d x)
      · rw [extendMat_apply_of_not_mem (hφ := hφ) (B := B) (x := x) (y := y) (Or.inl hx),
          extendMat_apply_of_not_mem (hφ := hφ)
            (B := Matrix.diagonal (fun k => (d (φ k) : K)) * B *
              Matrix.diagonal (fun k => (((d (φ k))⁻¹ : Kˣ) : K)))
            (x := x) (y := y) (Or.inl hx),
          Matrix.one_apply_ne (i := x) (j := y) hxy]
        simp

private theorem diagGL_scalar_E05 {K : Type} [Field K] (b : Kˣ) :
    diagGL ![b, b] = Matrix.GeneralLinearGroup.scalar (Fin 2) b := by
  apply Units.ext
  simp [diagGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar]

private theorem diagGL_scalar_comm_E05 {K : Type} [Field K] (b : Kˣ) (X : GL (Fin 2) K) :
    diagGL ![b, b] * X = X * diagGL ![b, b] := by
  rw [diagGL_scalar_E05 b]
  exact Matrix.GeneralLinearGroup.scalar_commute b X

private theorem diagGL_eq_scalar_mul_E05 {K : Type} [Field K] {c b : Kˣ} (hb : b ^ 2 = c⁻¹) :
    diagGL ![c⁻¹, 1] = Matrix.SpecialLinearGroup.toGL (plusDiagSL2 b) * diagGL ![b, b] := by
  have hbb : (b : K) * (b : K) = (c⁻¹ : K) := by
    have h := congrArg Units.val hb
    simpa [pow_two] using h
  apply Units.ext
  rw [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagGL, plusDiagSL2, Matrix.diagonal_mul_diagonal, hbb]

private theorem diagGL_conj_E05 {K : Type} [Field K] {c b : Kˣ} (hb : b ^ 2 = c⁻¹)
    (A : SL(2, K)) :
    diagGL ![c⁻¹, 1] * Matrix.SpecialLinearGroup.toGL A * (diagGL ![c⁻¹, 1])⁻¹ =
      Matrix.SpecialLinearGroup.toGL (plusDiagSL2 b) * Matrix.SpecialLinearGroup.toGL A *
        (Matrix.SpecialLinearGroup.toGL (plusDiagSL2 b))⁻¹ := by
  have hC : diagGL ![b, b] * Matrix.SpecialLinearGroup.toGL A * (diagGL ![b, b])⁻¹ =
      Matrix.SpecialLinearGroup.toGL A := by
    rw [diagGL_scalar_comm_E05 b (Matrix.SpecialLinearGroup.toGL A), mul_assoc,
      mul_inv_cancel, mul_one]
  have hassoc : (Matrix.SpecialLinearGroup.toGL (plusDiagSL2 b) * diagGL ![b, b]) *
      Matrix.SpecialLinearGroup.toGL A *
      (Matrix.SpecialLinearGroup.toGL (plusDiagSL2 b) * diagGL ![b, b])⁻¹ =
      Matrix.SpecialLinearGroup.toGL (plusDiagSL2 b) *
        (diagGL ![b, b] * Matrix.SpecialLinearGroup.toGL A * (diagGL ![b, b])⁻¹) *
        (Matrix.SpecialLinearGroup.toGL (plusDiagSL2 b))⁻¹ := by
    group
  rw [diagGL_eq_scalar_mul_E05 hb, hassoc, hC]

theorem orderOf_plusDiagSL2 {K : Type} [Field K] (b : Kˣ) :
    orderOf (plusDiagSL2 b) = orderOf b := by
  exact orderOf_injective (plusDiagSL2Hom_E05 K) (plusDiagSL2_injective_E05 (K := K)) b

theorem exists_sq_eq_inv_of_odd_orderOf {G : Type*} [Group G] {c : G} (hodd : Odd (orderOf c)) :
    ∃ b : G, b ^ 2 = c⁻¹ ∧ orderOf b = orderOf c := by
  obtain ⟨k, hk⟩ := hodd
  have hb : (c ^ k) ^ 2 = c⁻¹ := by
    rw [← pow_mul]
    have hp : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one c
    have h1 : c ^ (2 * k) * c = 1 := by rw [pow_succ] at hp; exact hp
    rw [show k * 2 = 2 * k by ring]
    exact eq_inv_of_mul_eq_one_left h1
  refine ⟨c ^ k, hb, ?_⟩
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  · apply orderOf_dvd_of_pow_eq_one
    have h1 : (c⁻¹) ^ orderOf (c ^ k) = 1 := by
      rw [← hb, ← pow_mul, show 2 * orderOf (c ^ k) = orderOf (c ^ k) * 2 by ring,
        pow_mul, pow_orderOf_eq_one, one_pow]
    rwa [inv_pow, inv_eq_one] at h1

theorem torusElt_mul_plusResExt_mul_inv {K : Type} [Field K] (a : Fin 3 → Kˣ)
    (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :
    torusElt 3 K a * plusResExt K (show 1 + 2 = 3 from rfl) g * (torusElt 3 K a)⁻¹ =
      plusResExt K (show 1 + 2 = 3 from rfl)
        (torusElt 2 K ![a 1, a 2] * g * (torusElt 2 K ![a 1, a 2])⁻¹) := by
  have htm : 1 + 2 = 3 := rfl
  have hf : (fun s : Fin 2 ⊕ Fin 2 => ((Sum.elim ![a 1, a 2] ![a 1, a 2]⁻¹ s : Kˣ) : K)) =
      fun s => ((Sum.elim a a⁻¹ (plusResIdx htm s) : Kˣ) : K) := by
    funext s
    rcases s with i | i <;> fin_cases i <;> simp [plusResIdx_inl, plusResIdx_inr]
  have hf' : (fun s : Fin 2 ⊕ Fin 2 => (((Sum.elim ![a 1, a 2] ![a 1, a 2]⁻¹ s)⁻¹ : Kˣ) : K)) =
      fun s => (((Sum.elim a a⁻¹ (plusResIdx htm s))⁻¹ : Kˣ) : K) := by
    funext s
    rcases s with i | i <;> fin_cases i <;> simp [plusResIdx_inl, plusResIdx_inr]
  have hL : autMat (torusElt 3 K a * plusResExt K htm g * (torusElt 3 K a)⁻¹) =
      Matrix.diagonal (fun x => ((Sum.elim a a⁻¹ x : Kˣ) : K)) *
        extendMat (plusResIdx_injective htm) (autMat g) *
        Matrix.diagonal (fun x => (((Sum.elim a a⁻¹ x)⁻¹ : Kˣ) : K)) := by
    rw [map_mul, map_mul, autMat_torusElt, autMat_plusResExt, autMat_inv_torusElt_E05]
  have hR : autMat (plusResExt K htm
      (torusElt 2 K ![a 1, a 2] * g * (torusElt 2 K ![a 1, a 2])⁻¹)) =
      extendMat (plusResIdx_injective htm)
        (Matrix.diagonal (fun s => ((Sum.elim a a⁻¹ (plusResIdx htm s) : Kˣ) : K)) * autMat g *
          Matrix.diagonal (fun s => (((Sum.elim a a⁻¹ (plusResIdx htm s))⁻¹ : Kˣ) : K))) := by
    rw [autMat_plusResExt, map_mul, map_mul, autMat_torusElt, autMat_inv_torusElt_E05, hf, hf']
  apply autMat_injective
  rw [hL, hR]
  exact diag_mul_extendMat_mul_diag_E05 (plusResIdx_injective htm) (Sum.elim a a⁻¹) (autMat g)

theorem torusElt_two_mul_plusIotaTwo_mul_inv {K : Type} [Field K] {c b : Kˣ} (hb : b ^ 2 = c⁻¹)
    (A : SL(2, K)) :
    torusElt 2 K ![c⁻¹, 1] * plusIotaTwo K A * (torusElt 2 K ![c⁻¹, 1])⁻¹ =
      plusIotaTwo K (plusDiagSL2 b * A * (plusDiagSL2 b)⁻¹) := by
  change torusElt 2 K ![c⁻¹, 1] * levi 2 K (Matrix.SpecialLinearGroup.toGL A) *
      (torusElt 2 K ![c⁻¹, 1])⁻¹ =
    levi 2 K (Matrix.SpecialLinearGroup.toGL (plusDiagSL2 b * A * (plusDiagSL2 b)⁻¹))
  rw [torusElt_eq_levi, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  rw [map_mul, map_mul, map_inv]
  exact diagGL_conj_E05 hb A

theorem torusElt_mul_plusRootEmbTwo_mul_inv {K : Type} [Field K] {c b : Kˣ} (hb : b ^ 2 = c⁻¹)
    (A : SL(2, K)) :
    torusElt 3 K ![c, c⁻¹, 1] * plusRootEmbTwo K A * (torusElt 3 K ![c, c⁻¹, 1])⁻¹ =
      plusRootEmbTwo K (plusDiagSL2 b * A * (plusDiagSL2 b)⁻¹) := by
  change torusElt 3 K ![c, c⁻¹, 1] * plusResExt K (show 1 + 2 = 3 from rfl) (plusIotaTwo K A) *
      (torusElt 3 K ![c, c⁻¹, 1])⁻¹ =
    plusResExt K (show 1 + 2 = 3 from rfl)
      (plusIotaTwo K (plusDiagSL2 b * A * (plusDiagSL2 b)⁻¹))
  rw [torusElt_mul_plusResExt_mul_inv (a := ![c, c⁻¹, 1]) (g := plusIotaTwo K A)]
  have hv : (![![c, c⁻¹, 1] 1, ![c, c⁻¹, 1] 2] : Fin 2 → Kˣ) = ![c⁻¹, 1] := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  exact congrArg (plusResExt K (show 1 + 2 = 3 from rfl))
    (torusElt_two_mul_plusIotaTwo_mul_inv (c := c) (b := b) hb A)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
