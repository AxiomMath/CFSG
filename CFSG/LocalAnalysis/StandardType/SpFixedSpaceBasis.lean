module

public import CFSG.LocalAnalysis.StandardType.SpFixedNorm
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.StandardType

namespace SpFixed

open Matrix
open CFSG.Open (StatedSp)

variable {F : Type} [Field F] {n : ℕ}

private noncomputable def spForm (F : Type) [Field F] (n : ℕ) :
    LinearMap.BilinForm F (Fin n ⊕ Fin n → F) :=
  Matrix.toBilin' (gram F n)

@[simp] private theorem spForm_apply (x y : Fin n ⊕ Fin n → F) :
    spForm F n x y = x ⬝ᵥ gram F n *ᵥ y :=
  Matrix.toBilin'_apply' _ _ _

private theorem spForm_isAlt : (spForm F n).IsAlt := by
  intro x
  rw [spForm_apply, gram, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, add_zero, zero_add]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [Function.comp_apply, dotProduct, Sum.elim_inl, Sum.elim_inr,
    Matrix.neg_mulVec, Pi.neg_apply, one_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k _
  simp only [Function.comp_apply, Matrix.one_mulVec]
  ring

private theorem J_eq_gram [CharP F 2] (n : ℕ) : Matrix.J (Fin n) F = gram F n := by
  ext (i | i) (j | j) <;> simp [Matrix.J, gram, CharTwo.neg_eq]

private theorem spForm_nondegenerate [CharP F 2] : (spForm F n).Nondegenerate := by
  have hmul : gram F n * gram F n = 1 := by
    rw [gram, Matrix.fromBlocks_multiply]
    ext (i | i) (j | j) <;>
      simp [Matrix.one_apply, CharTwo.neg_eq]
  have hdet1 : (gram F n).det * (gram F n).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have hdet : (gram F n).det ≠ 0 := fun h => by
    rw [h, mul_zero] at hdet1
    exact one_ne_zero hdet1.symm
  rw [spForm]
  exact Matrix.nondegenerate_toBilin'_iff.mpr
    (Matrix.nondegenerate_iff_det_ne_zero.mpr hdet)

private theorem spForm_fixedNorm_adjoint (D : Subgroup (StatedSp n F)) [Fintype D]
    (x y : Fin n ⊕ Fin n → F) :
    spForm F n (fixedNorm D *ᵥ x) y = spForm F n x (fixedNorm D *ᵥ y) := by
  rw [spForm_apply, spForm_apply]
  calc (fixedNorm D *ᵥ x) ⬝ᵥ gram F n *ᵥ y
      = ((fixedNorm D *ᵥ x) ᵥ* gram F n) ⬝ᵥ y := by rw [Matrix.dotProduct_mulVec]
    _ = (x ᵥ* ((fixedNorm D)ᵀ * gram F n)) ⬝ᵥ y := by rw [Matrix.vecMul_mulVec]
    _ = (x ᵥ* (gram F n * fixedNorm D)) ⬝ᵥ y := by rw [fixedNorm_transpose_mul_gram]
    _ = x ⬝ᵥ ((gram F n * fixedNorm D) *ᵥ y) := by rw [Matrix.dotProduct_mulVec]
    _ = x ⬝ᵥ (gram F n *ᵥ (fixedNorm D *ᵥ y)) := by rw [Matrix.mulVec_mulVec]

private theorem mulVec_fixedNorm_fixed (D : Subgroup (StatedSp n F)) [Fintype D] [CharP F 2]
    (hodd : Odd (Fintype.card D)) {u : Fin n ⊕ Fin n → F}
    (hu : u ∈ LinearMap.range (Matrix.mulVecLin (fixedNorm D))) :
    fixedNorm D *ᵥ u = u := by
  obtain ⟨v, hv⟩ := hu
  rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    fixedNorm_mul_fixedNorm D hodd]

theorem exists_symplectic_basis_of_fixedNorm [CharP F 2] (D : Subgroup (StatedSp n F)) [Fintype D]
    (hodd : Odd (Fintype.card D)) :
    ∃ (m : ℕ) (B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F),
      Bᵀ * gram F n * B = gram F m ∧ fixedNorm D * B = B ∧
        ∀ x : Fin n ⊕ Fin n → F, ∃ c : Fin m ⊕ Fin m → F, fixedNorm D *ᵥ x = B *ᵥ c := by
  classical
  set U : Submodule F (Fin n ⊕ Fin n → F) :=
    LinearMap.range (Matrix.mulVecLin (fixedNorm D)) with hU
  have hUmem : ∀ u : Fin n ⊕ Fin n → F, u ∈ U ↔ ∃ v, fixedNorm D *ᵥ v = u := by
    intro u
    simp [hU, LinearMap.mem_range]
  have hUalt : ((spForm F n).restrict U).IsAlt :=
    fun x => by simpa using (spForm_isAlt (F := F) (n := n)).self_eq_zero (x : Fin n ⊕ Fin n → F)
  have hUnd : ((spForm F n).restrict U).Nondegenerate := by
    have hrefl : ((spForm F n).restrict U).IsRefl := hUalt.isRefl
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr ?_
    intro x hx
    apply Subtype.ext
    refine (spForm_nondegenerate (F := F) (n := n)).1 (x : Fin n ⊕ Fin n → F) fun y => ?_
    calc spForm F n (x : Fin n ⊕ Fin n → F) y
        = spForm F n (fixedNorm D *ᵥ (x : Fin n ⊕ Fin n → F)) y := by
          rw [mulVec_fixedNorm_fixed D hodd x.2]
      _ = spForm F n (x : Fin n ⊕ Fin n → F) (fixedNorm D *ᵥ y) :=
          spForm_fixedNorm_adjoint D (x : _) y
      _ = 0 := by
          have hy : fixedNorm D *ᵥ y ∈ U := (hUmem _).mpr ⟨y, rfl⟩
          simpa using hx ⟨fixedNorm D *ᵥ y, hy⟩
  obtain ⟨m, b, hbJ⟩ :=
    LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J (B := (spForm F n).restrict U) hUalt hUnd
  let B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F :=
    Matrix.of fun i j => (b j : Fin n ⊕ Fin n → F) i
  refine ⟨m, B, ?_, ?_, ?_⟩
  · have hBcol : ∀ j : Fin m ⊕ Fin m, B *ᵥ Pi.single j 1 = (b j : Fin n ⊕ Fin n → F) := by
      intro j
      rw [Matrix.mulVec_single_one]
      rfl
    have hkey : ∀ j j' : Fin m ⊕ Fin m,
        spForm F n (b j : Fin n ⊕ Fin n → F) (b j' : Fin n ⊕ Fin n → F) =
          (Bᵀ * gram F n * B) j j' := by
      intro j j'
      have h := DFunLike.congr_fun (DFunLike.congr_fun (Matrix.toBilin'_comp (gram F n) B B)
        (Pi.single j 1)) (Pi.single j' 1)
      simpa [spForm, Matrix.toLin'_apply, hBcol j, hBcol j'] using h
    have hbJentry : ∀ j j' : Fin m ⊕ Fin m,
        spForm F n (b j : Fin n ⊕ Fin n → F) (b j' : Fin n ⊕ Fin n → F) =
          Matrix.J (Fin m) F j j' := by
      intro j j'
      have h := congrFun (congrFun hbJ j) j'
      simpa using h
    rw [← J_eq_gram (F := F) m]
    ext j j'
    rw [← hkey j j']
    exact hbJentry j j'
  · have hNB : fixedNorm D * B = B := by
      ext i j
      have hfix : fixedNorm D *ᵥ (b j : Fin n ⊕ Fin n → F) = (b j : Fin n ⊕ Fin n → F) :=
        mulVec_fixedNorm_fixed D hodd (b j).2
      rw [Matrix.mul_apply]
      trans (fixedNorm D *ᵥ (b j : Fin n ⊕ Fin n → F)) i
      · simp [Matrix.mulVec, dotProduct, B]
      · rw [hfix]
        simp [B]
    exact hNB
  · intro x
    have hxU : fixedNorm D *ᵥ x ∈ U := (hUmem _).mpr ⟨x, rfl⟩
    refine ⟨b.equivFun ⟨fixedNorm D *ᵥ x, hxU⟩, ?_⟩
    have hBc : ∀ c : Fin m ⊕ Fin m → F,
        B *ᵥ c = ((b.equivFun.symm c : U) : Fin n ⊕ Fin n → F) := by
      intro c
      simp only [b.equivFun_symm_apply]
      ext i
      simp only [Matrix.mulVec, dotProduct, B, Matrix.of_apply,
        Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hBc, b.equivFun.symm_apply_apply]

end SpFixed

end CFSG.StandardType
