module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Basic
public import CFSG.RankThree.SubgroupLists.OrthogonalForms
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneIrredFive
import CFSG.RankThree.PartOne.N1322.CaseBasic
import CFSG.RankThree.PartOne.N1322.CoreHyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.ZS.DimThree

open Subgroup Matrix CFSG.RankThree.PartOne CFSG.RankThree.SubgroupLists
open CFSG.RepresentationTheory
open CFSG.RankThree.PartOne.LIT (autGL autGL_mulVec)
open CFSG.ComponentClassification.UnbalancedGS.SwappedCentralProduct
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] noncomputable def formOf (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    (M : Matrix (Fin 3) (Fin 3) (ZMod p)) : QuadraticForm (ZMod p) U :=
  (Matrix.toQuadraticMap' M).comp (e : U →ₗ[ZMod p] (Fin 3 → ZMod p))

theorem formOf_apply (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p)) (M : Matrix (Fin 3) (Fin 3) (ZMod p))
    (u : U) : formOf e M u = e u ⬝ᵥ (M *ᵥ e u) := by
  simp only [formOf, QuadraticMap.comp_apply, Matrix.toQuadraticMap', Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  rfl

private lemma polar_dotProduct_mulVec_zf {K : Type*} [CommRing K]
    (M : Matrix (Fin 3) (Fin 3) K) (x y : Fin 3 → K) :
    (x + y) ⬝ᵥ (M *ᵥ (x + y)) - x ⬝ᵥ (M *ᵥ x) - y ⬝ᵥ (M *ᵥ y) =
      x ⬝ᵥ (M *ᵥ y) + y ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  abel

private lemma polar_formOf_zf (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (u v : U) :
    QuadraticMap.polar (formOf e M) u v = (2 : ZMod p) * (e u ⬝ᵥ (M *ᵥ e v)) := by
  simp only [QuadraticMap.polar, formOf_apply, map_add]
  rw [polar_dotProduct_mulVec_zf]
  have hsym : e v ⬝ᵥ (M *ᵥ e u) = e u ⬝ᵥ (M *ᵥ e v) := by
    rw [← Matrix.dotProduct_transpose_mulVec (A := M) (x := e u) (y := e v), hMt]
  rw [hsym]
  ring

theorem polarBilin_formOf_nondegenerate (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0) :
    (QuadraticMap.polarBilin (formOf e M)).Nondegenerate := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hsep : ∀ u : U, (∀ v, QuadraticMap.polarBilin (formOf e M) u v = 0) → u = 0 := by
    intro u hu
    have hu0 : e u = 0 := by
      refine Matrix.Nondegenerate.eq_zero_of_ortho (Matrix.nondegenerate_of_det_ne_zero hMd)
        (fun w => ?_)
      have h := hu (e.symm w)
      rw [QuadraticMap.polarBilin_apply_apply, polar_formOf_zf e hMt, e.apply_symm_apply] at h
      exact (mul_eq_zero.mp h).resolve_left h2
    have h : e.symm (e u) = e.symm 0 := congrArg e.symm hu0
    simpa using h
  refine ⟨hsep, ?_⟩
  intro v hv
  refine hsep v (fun u => ?_)
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  exact hv u

private lemma dotProduct_mulVec_transpose_mul_zf (G M : Matrix (Fin 3) (Fin 3) (ZMod p))
    (x : Fin 3 → ZMod p) :
    (G *ᵥ x) ⬝ᵥ (M *ᵥ (G *ᵥ x)) = x ⬝ᵥ ((Gᵀ * M * G) *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]

private lemma eq_of_forall_dotProduct_mulVec_zf (hp : p ≠ 2)
    {N M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hN : Nᵀ = N) (hM : Mᵀ = M)
    (h : ∀ x, x ⬝ᵥ (N *ᵥ x) = x ⬝ᵥ (M *ᵥ x)) : N = M := by
  let _ : NeZero (2 : ZMod p) := ⟨ZMod.prime_ne_zero p 2 hp⟩
  have hN' : N.toBilin'.IsSymm := (Matrix.isSymm_toBilin'_iff_isSymm).mpr hN
  have hM' : M.toBilin'.IsSymm := (Matrix.isSymm_toBilin'_iff_isSymm).mpr hM
  have heq : N.toBilin' = M.toBilin' :=
    (LinearMap.BilinForm.ext_iff_of_isSymm hN' hM').mpr fun x => by
      simpa only [Matrix.toBilin'_apply'] using h x
  exact (Matrix.toBilin' (n := Fin 3) (R₁ := ZMod p)).injective heq

theorem isIsom_formOf_iff (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (g : U ≃ₗ[ZMod p] U) :
    IsIsom p (formOf e M) g ↔
      ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
        ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = M := by
  set G : Matrix (Fin 3) (Fin 3) (ZMod p) :=
    ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) with hG
  have hmv : ∀ x : Fin 3 → ZMod p, G *ᵥ x = e (g (e.symm x)) := by
    intro x
    rw [hG]
    exact autGL_mulVec e g x
  constructor
  · intro h
    have hN : (Gᵀ * M * G)ᵀ = Gᵀ * M * G := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hMt,
        Matrix.mul_assoc]
    refine eq_of_forall_dotProduct_mulVec_zf hp hN hMt (fun x => ?_)
    have hv := h (e.symm x)
    rw [formOf_apply, formOf_apply, e.apply_symm_apply, ← hmv x] at hv
    exact (dotProduct_mulVec_transpose_mul_zf G M x).symm.trans hv
  · intro hN v
    have hx : e (g v) = G *ᵥ e v := by
      have h := hmv (e v)
      rw [LinearEquiv.symm_apply_apply] at h
      exact h.symm
    rw [formOf_apply, formOf_apply, hx, dotProduct_mulVec_transpose_mul_zf, hN]

private lemma scalar_eq_one_zf {M : Matrix (Fin 3) (Fin 3) (ZMod p)}
    {A : Matrix (Fin 3) (Fin 3) (ZMod p)} {l : ZMod p} (hMd : M.det ≠ 0)
    (hl : Aᵀ * M * A = l • M) (hAA : A * A = 1) (hdetA : A.det = -1) : l = 1 := by
  have hMne : M ≠ 0 := by
    rintro rfl
    exact hMd (by simp)
  have h1 : Aᵀ * (Aᵀ * M * A) * A = M := by
    calc Aᵀ * (Aᵀ * M * A) * A = (A * A)ᵀ * M * (A * A) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = M := by rw [hAA]; simp
  have h2 : Aᵀ * (Aᵀ * M * A) * A = (l * l) • M := by
    rw [hl, Matrix.mul_smul, Matrix.smul_mul, hl, smul_smul]
  have hsq_l : M = (l * l) • M := h1.symm.trans h2
  have h3 : (l * l - 1) • M = 0 := by
    rw [sub_smul, one_smul, ← hsq_l]
    exact sub_self M
  have hl2 : l * l = 1 := sub_eq_zero.mp ((smul_eq_zero_iff_left hMne).mp h3)
  have hl3 : l ^ 3 = 1 := by
    have h := congrArg Matrix.det hl
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetA, Matrix.det_smul,
      Fintype.card_fin] at h
    have h' : M.det = l ^ 3 * M.det := by
      calc M.det = (-1 : ZMod p) * M.det * (-1) := by ring
        _ = l ^ 3 * M.det := h
    have h4 : (1 : ZMod p) * M.det = l ^ 3 * M.det := by rwa [one_mul]
    exact (mul_right_cancel₀ hMd h4).symm
  calc l = l * (l * l) := by rw [hl2, mul_one]
    _ = l ^ 3 := by ring
    _ = 1 := hl3

theorem isIsom_of_isRefl_of_normalizes (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    (hirr : IsIrreducibleMatrixRep (omegaGL M).subtype) {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    (hn : ∀ x ∈ omegaGL M, autGL e t * x * (autGL e t)⁻¹ ∈ omegaGL M) :
    IsIsom p (formOf e M) t := by
  set A : Matrix (Fin 3) (Fin 3) (ZMod p) :=
    ((autGL e t : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) with hA
  obtain ⟨l, hl⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.exists_smul_transpose_mul_of_normalizes_omegaGL
      hp hMt hMd hirr hn
  have hl' : Aᵀ * M * A = l • M := by rw [hA]; exact hl
  have hrefl : N1322.IsRefl (autGL e t) := (isRefl_iff_autGL hp e t).mp ht
  have hdetA : A.det = -1 := by
    rw [hA]
    exact N1322.IsRefl.det_eq hrefl
  have hAA : A * A = 1 := by
    have h := congrArg (fun u : GL (Fin 3) (ZMod p) =>
      (u : Matrix (Fin 3) (Fin 3) (ZMod p))) (N1322.IsRefl.sq hrefl)
    rw [hA]
    simpa using h
  have hl1 : l = 1 := scalar_eq_one_zf hMd hl' hAA hdetA
  refine (isIsom_formOf_iff hp e hMt t).mpr ?_
  rw [← hA, hl', hl1, one_smul]

private lemma eq_neg_one_mul_neg_one_mul_zf {K : Type*} [Field K] (x : GL (Fin 3) K) :
    x = (-1 : GL (Fin 3) K) * ((-1 : GL (Fin 3) K) * x) := by
  rw [← mul_assoc, N1322.neg_one_mul_neg_one, one_mul]

private lemma det_eq_one_or_neg_one_zf (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    {g : U ≃ₗ[ZMod p] U} (hg : IsIsom p (formOf e M) g) :
    ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 ∨
      ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).det = -1 := by
  have hG := (isIsom_formOf_iff hp e hMt g).mp hg
  have h := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hsq : (((autGL e g : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)).det) ^ 2 = 1 := by
    have h' : (((autGL e g : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)).det) ^ 2 * M.det = 1 * M.det := by
      calc (((autGL e g : GL (Fin 3) (ZMod p)) :
            Matrix (Fin 3) (Fin 3) (ZMod p)).det) ^ 2 * M.det
          = ((autGL e g : GL (Fin 3) (ZMod p)) :
              Matrix (Fin 3) (Fin 3) (ZMod p)).det * M.det *
              ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).det := by
            ring
        _ = M.det := h
        _ = 1 * M.det := by rw [one_mul]
    exact mul_right_cancel₀ hMd h'
  rw [sq_eq_one_iff] at hsq
  exact hsq

private lemma neg_one_mul_mem_soGL_zf {M : Matrix (Fin 3) (Fin 3) (ZMod p)}
    {A : GL (Fin 3) (ZMod p)}
    (h1 : (A : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
      (A : Matrix (Fin 3) (Fin 3) (ZMod p)) = M)
    (h2 : (A : Matrix (Fin 3) (Fin 3) (ZMod p)).det = -1) :
    (-1 : GL (Fin 3) (ZMod p)) * A ∈ soGL M := by
  rw [mem_soGL]
  have hv : ((↑((-1 : GL (Fin 3) (ZMod p)) * A) : Matrix (Fin 3) (Fin 3) (ZMod p)))
      = -(↑A) := by
    rw [Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]
  constructor
  · rw [hv]
    simp only [Matrix.transpose_neg, neg_mul, mul_neg, neg_neg]
    exact h1
  · rw [hv, Matrix.det_neg, Fintype.card_fin, h2]
    ring

theorem autGL_commutator_mem_omegaGL (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    {g h : U ≃ₗ[ZMod p] U} (hg : IsIsom p (formOf e M) g) (hh : IsIsom p (formOf e M) h) :
    autGL e (g * h * g⁻¹ * h⁻¹) ∈ omegaGL M := by
  have hG' : ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
      ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = M :=
    (isIsom_formOf_iff hp e hMt g).mp hg
  have hH' : ((autGL e h : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
      ((autGL e h : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = M :=
    (isIsom_formOf_iff hp e hMt h).mp hh
  have hGdet := det_eq_one_or_neg_one_zf hp e hMt hMd hg
  have hHdet := det_eq_one_or_neg_one_zf hp e hMt hMd hh
  have hmap : autGL e (g * h * g⁻¹ * h⁻¹) = ⁅(autGL e g), (autGL e h)⁆ := by
    simp [commutatorElement_def]
  rw [hmap]
  rcases hGdet with hGd | hGd <;> rcases hHdet with hHd | hHd
  · have hS : autGL e g ∈ soGL M := mem_soGL.mpr ⟨hG', hGd⟩
    have hT : autGL e h ∈ soGL M := mem_soGL.mpr ⟨hH', hHd⟩
    exact Subgroup.commutator_mem_commutator hS hT
  · have hS : autGL e g ∈ soGL M := mem_soGL.mpr ⟨hG', hGd⟩
    have hT : (-1 : GL (Fin 3) (ZMod p)) * autGL e h ∈ soGL M :=
      neg_one_mul_mem_soGL_zf hH' hHd
    rw [eq_neg_one_mul_neg_one_mul_zf (autGL e h),
      commutatorElement_mul_central_right N1322.neg_one_comm (autGL e g) ((-1) * autGL e h)]
    exact Subgroup.commutator_mem_commutator hS hT
  · have hS : (-1 : GL (Fin 3) (ZMod p)) * autGL e g ∈ soGL M :=
      neg_one_mul_mem_soGL_zf hG' hGd
    have hT : autGL e h ∈ soGL M := mem_soGL.mpr ⟨hH', hHd⟩
    rw [eq_neg_one_mul_neg_one_mul_zf (autGL e g),
      commutatorElement_central_mul_left N1322.neg_one_comm ((-1) * autGL e g) (autGL e h)]
    exact Subgroup.commutator_mem_commutator hS hT
  · have hS : (-1 : GL (Fin 3) (ZMod p)) * autGL e g ∈ soGL M :=
      neg_one_mul_mem_soGL_zf hG' hGd
    have hT : (-1 : GL (Fin 3) (ZMod p)) * autGL e h ∈ soGL M :=
      neg_one_mul_mem_soGL_zf hH' hHd
    rw [eq_neg_one_mul_neg_one_mul_zf (autGL e g), eq_neg_one_mul_neg_one_mul_zf (autGL e h),
      commutatorElement_central_mul_left N1322.neg_one_comm ((-1) * autGL e g)
        ((-1) * ((-1) * autGL e h)),
      commutatorElement_mul_central_right N1322.neg_one_comm ((-1) * autGL e g)
        ((-1) * autGL e h)]
    exact Subgroup.commutator_mem_commutator hS hT

end CFSG.StandardType.ZS.DimThree
