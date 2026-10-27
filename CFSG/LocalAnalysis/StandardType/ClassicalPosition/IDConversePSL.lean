module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.LocalAnalysis.StandardType.GGRootDetectCore

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.LieType.Universal CFSG.StandardType

private lemma exists_conjSL_diag {k : ℕ} {F : Type} [Field F] {X : Type} [Group X]
    (φ : Matrix.SpecialLinearGroup (Fin (k + 1)) F →* X) {b : X}
    {t : GL (Fin (k + 1)) F}
    (hb : ∀ y, b⁻¹ * φ y * b = φ (InnerDiagA.conjSL t y)) :
    ∃ (e : Fin (k + 1) → F) (D : GL (Fin (k + 1)) F)
      (A₀ : Matrix.SpecialLinearGroup (Fin (k + 1)) F),
      (∀ l, e l ≠ 0) ∧
        (D : Matrix (Fin (k + 1)) (Fin (k + 1)) F) = Matrix.diagonal e ∧
        (∀ z, (b * φ A₀)⁻¹ * φ z * (b * φ A₀) = φ (InnerDiagA.conjSL D z)) := by
  classical
  set d : F := (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det with hd
  have hd0 : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero t
  set e : Fin (k + 1) → F := fun l => if l = 0 then d else 1 with he
  have he0 : ∀ l, e l ≠ 0 := fun l => by
    simp only [e]
    split_ifs
    exacts [hd0, one_ne_zero]
  have hdetD : (Matrix.diagonal e).det = d := by
    rw [Matrix.det_diagonal]
    simp [e]
  set D : GL (Fin (k + 1)) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal e)
    (by rw [hdetD]; exact hd0)
  have hDval : (D : Matrix (Fin (k + 1)) (Fin (k + 1)) F) = Matrix.diagonal e := rfl
  have hdet1 : Matrix.GeneralLinearGroup.det (t * D⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      hDval, hdetD, ← hd]
  obtain ⟨A₀, hA₀⟩ : t * D⁻¹ ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (k + 1)) F →* GL (Fin (k + 1)) F).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet1
  have hconjGL : ∀ (A : GL (Fin (k + 1)) F)
      (u : Matrix.SpecialLinearGroup (Fin (k + 1)) F),
      A * Matrix.SpecialLinearGroup.toGL u * A⁻¹ =
        Matrix.SpecialLinearGroup.toGL (InnerDiagA.conjSL A u) := by
    intro A u
    apply Units.ext
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      InnerDiagA.coe_conjSL]
  refine ⟨e, D, A₀, he0, hDval, fun z => ?_⟩
  calc (b * φ A₀)⁻¹ * φ z * (b * φ A₀)
      = (φ A₀)⁻¹ * (b⁻¹ * φ z * b) * φ A₀ := by group
    _ = (φ A₀)⁻¹ * φ (InnerDiagA.conjSL t z) * φ A₀ := by rw [hb]
    _ = φ (A₀⁻¹ * InnerDiagA.conjSL t z * A₀) := by
          rw [← map_inv, ← map_mul, ← map_mul]
    _ = φ (InnerDiagA.conjSL D z) := by
          congr 1
          apply Matrix.SpecialLinearGroup.toGL_injective
          rw [map_mul, map_mul, map_inv, ← hconjGL t z, ← hconjGL D z, hA₀]
          group

theorem ggPsiInnerDiag_of_conjSL {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {X : Type} [Group X] (φ : Matrix.SpecialLinearGroup (Fin (k + 1)) F →* X) {b : X}
    {t : GL (Fin (k + 1)) F} (hb : ∀ y, b⁻¹ * φ y * b = φ (InnerDiagA.conjSL t y)) :
    GGPsiInnerDiag (SpecialLinear.rootDatum k F) φ b := by
  classical
  obtain ⟨e, D, A₀, he0, hDval, hconjD⟩ := exists_conjSL_diag (k := k) φ hb
  refine ⟨φ A₀, ⟨A₀, rfl⟩, fun γ hγ => ?_⟩
  have hidx := (SpecialLinear.idx_spec k hγ).1
  set i := (SpecialLinear.idx k γ).1 with hi
  set j := (SpecialLinear.idx k γ).2 with hj
  have hij : i ≠ j := by simpa [hi, hj] using hidx
  set lam : F := e i * (e j)⁻¹ with hlam
  have hlam0 : lam ≠ 0 := mul_ne_zero (he0 i) (inv_ne_zero (he0 j))
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) lam
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hμ
    exact hlam0 hμ
  set e' : Fin (k + 1) → F :=
    fun l => (if l = i then μ else 1) * (if l = j then μ⁻¹ else 1) with he'
  have he'0 : ∀ l, e' l ≠ 0 := fun l => by
    simp only [e']
    refine mul_ne_zero ?_ ?_ <;> split_ifs
    exacts [hμ0, one_ne_zero, inv_ne_zero hμ0, one_ne_zero]
  have hdet' : (Matrix.diagonal e').det = 1 := by
    rw [Matrix.det_diagonal]
    simp only [e', Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    exact mul_inv_cancel₀ hμ0
  let h : Matrix.SpecialLinearGroup (Fin (k + 1)) F := ⟨Matrix.diagonal e', hdet'⟩
  have hh : ((Matrix.SpecialLinearGroup.toGL h : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) = Matrix.diagonal e' := rfl
  refine ⟨h, HypSixTypeA.mem_ggTorus_of_diagonal he'0 hh, fun z hz => ?_⟩
  change z ∈ SpecialLinear.rootGroup k F γ at hz
  rw [SpecialLinear.rootGroup_eq_idx k F hγ] at hz
  obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij z).mp hz
  let d' : Fin (k + 1) → Fˣ := fun l => Units.mk0 (e l) (he0 l)
  have hD_eq : D = InnerDiagA.diagGL d' := by
    apply Units.ext
    rw [hDval, InnerDiagA.coe_diagGL]
    apply Matrix.diagonal_injective
    funext l
    simp [d']
  have hDz : InnerDiagA.conjSL D (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij (e i * c * (e j)⁻¹) := by
    rw [hD_eq, InnerDiagA.conjSL_diagGL_transvection d' hij c]
    congr 2
  have hhz : h * Matrix.SpecialLinearGroup.transvection hij c * h⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (e' i * c * (e' j)⁻¹) :=
    HypSixTypeA.sl_diag_conj_transvection he'0 hh hij c
  rw [hconjD, hDz, hhz]
  congr 2
  rw [show e' i = μ by simp [e', hij],
    show e' j = μ⁻¹ by simp [e', hij.symm]]
  calc e i * c * (e j)⁻¹ = c * lam := by rw [hlam]; ring
    _ = c * (μ * μ) := by rw [hμ]
    _ = μ * c * (μ⁻¹)⁻¹ := by rw [inv_inv]; ring

end CFSG.StandardType.ClassicalPosition
