module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SUOHinf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mBorel
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusRes
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock (orthParab orthBlockHom orthResHom orthBlockMat orthCoefMat
  orthCoefMat_apply orthBlockIdx orthBlockIdx_val orthBlockIdx_injective orthResMat orthResIncl
  orthResProj orthResHom_apply orthResMat_apply orthResIncl_apply orthResProj_apply
  orthResHom_mem_orthogonalGroup coe_orthBlockHom)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

@[expose] noncomputable def om6mChi (b c : K) :
    ↥(orthParab 2 (minusTailForm K b c) ![0, 2]) →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (orthBlockHom (minusTailForm K b c) om6m_orthCuts_zero_two 0)

private lemma om6m_orthCoefMat_tailDiag_D08 {t : Fin 2 → Kˣ}
    {k : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} :
    orthCoefMat (A := Fin 2 → K) (tailDiag 2 t k) =
      Matrix.diagonal (fun i => (t i : K)) := by
  ext i j
  rw [orthCoefMat_apply, tailDiag_apply]
  simp only [hypVec, torusElt_apply, Pi.single_apply, Sum.elim_inl, Matrix.diagonal_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h, Sum.inl.injEq]

private lemma om6m_orthBlockMat_tailDiag_D08 {t : Fin 2 → Kˣ}
    {k : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} :
    orthBlockMat om6m_orthCuts_zero_two 0 (tailDiag 2 t k) =
      Matrix.diagonal (fun i => (t (orthBlockIdx om6m_orthCuts_zero_two 0 i) : K)) := by
  rw [orthBlockMat, om6m_orthCoefMat_tailDiag_D08]
  exact Matrix.submatrix_diagonal (fun i => (t i : K)) (orthBlockIdx om6m_orthCuts_zero_two 0)
    (orthBlockIdx_injective om6m_orthCuts_zero_two 0)

theorem coe_om6mChi_of_tailDiag {t : Fin 2 → Kˣ} {k : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    {g : ↥(orthParab 2 (minusTailForm K b c) ![0, 2])}
    (hgd : ((g : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))) :
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) =
        tailDiag 2 t k) :
    ((om6mChi b c g : Kˣ) : K) = (t 0 : K) * t 1 := by
  unfold om6mChi
  rw [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, coe_orthBlockHom, hgd,
    om6m_orthBlockMat_tailDiag_D08, Matrix.det_diagonal]
  have hb : Function.Bijective (orthBlockIdx om6m_orthCuts_zero_two 0) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨orthBlockIdx_injective om6m_orthCuts_zero_two 0, by decide⟩
  rw [Function.Bijective.prod_comp hb (fun j : Fin 2 => (t j : K)), Fin.prod_univ_two]

theorem om6m_orthResHom_tailDiag {t : Fin 2 → Kˣ} {k : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    {g : ↥(orthParab 2 (minusTailForm K b c) ![0, 2])}
    (hgd : ((g : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))) :
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) =
        tailDiag 2 t k) :
    orthResHom (minusTailForm K b c) om6m_orthCuts_zero_two g = tailDiag 0 ![] k := by
  refine LinearEquiv.ext fun u => ?_
  rw [orthResHom_apply, orthResMat_apply, orthResIncl_apply, hgd, tailDiag_apply,
    orthResProj_apply]
  exact Prod.ext (funext fun c => by rcases c with i | i <;> exact i.elim0) rfl

theorem om6m_isSolvable_orthogonalGroup_quadTail_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadTail 0 (minusTailForm K b c))) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm K b c))
  haveI hder : Group.IsSolvable ↥(CFSG.AGLEmbedding.LeviBlock.orthResDer K b c 0) :=
    CFSG.AGLEmbedding.LeviBlock.isSolvable_orthResDer_zero hirr
  haveI hder' : Group.IsSolvable ↥⁅O, O⁆ := hder
  let e : ↥(commutator ↥O) ≃* ↥⁅O, O⁆ :=
    (Subgroup.equivMapOfInjective (commutator ↥O) O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator O))
  have hcomm : Group.IsSolvable ↥(commutator ↥O) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact (Group.isSolvable_commutator_iff (G := ↥O)).mp hcomm

theorem om6m_isSolvable_range_orthResHom (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Group.IsSolvable ↥(orthResHom (minusTailForm K b c) om6m_orthCuts_zero_two).range := by
  let O : Subgroup (((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K))) :=
    TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm K b c))
  have hle : (orthResHom (minusTailForm K b c) om6m_orthCuts_zero_two).range ≤ O := by
    rintro x ⟨y, rfl⟩
    exact orthResHom_mem_orthogonalGroup om6m_orthCuts_zero_two y
  letI : Group ↥O := Subgroup.toGroup O
  haveI hO : Group.IsSolvable ↥O :=
    om6m_isSolvable_orthogonalGroup_quadTail_zero (b := b) (c := c) hirr
  let f : ↥(orthResHom (minusTailForm K b c) om6m_orthCuts_zero_two).range →* ↥O :=
    Subgroup.inclusion hle
  have hf : Function.Injective f := Subgroup.inclusion_injective hle
  exact Group.isSolvable_of_isSolvable_injective (f := f) hf

theorem om6m_tailDiag_of_mem_hinf (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {t : Fin 2 → Kˣ} {k : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    {g : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (hg : g ∈ Hinf (orthParab 2 (minusTailForm K b c) ![0, 2]))
    (hgd : (g : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) =
      tailDiag 2 t k) :
    (t 0 : K) * t 1 = 1 ∧ k = 1 := by
  obtain ⟨hQ, h1⟩ := suo_hom_eq_one_of_mem_hinf (om6mChi b c) inferInstance hg
  obtain ⟨_, h2⟩ := suo_hom_eq_one_of_mem_hinf
    (orthResHom (minusTailForm K b c) om6m_orthCuts_zero_two)
    (om6m_isSolvable_range_orthResHom (b := b) (c := c) hirr) hg
  let gQ : ↥(orthParab 2 (minusTailForm K b c) ![0, 2]) := ⟨g, hQ⟩
  have hgdQ : ((gQ : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))) :
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) =
        tailDiag 2 t k := hgd
  have h1Q : om6mChi b c gQ = 1 := h1
  have h2Q : orthResHom (minusTailForm K b c) om6m_orthCuts_zero_two gQ = 1 := h2
  have hchi := coe_om6mChi_of_tailDiag (b := b) (c := c) (t := t) (k := k) (g := gQ) hgdQ
  have htprod : (t 0 : K) * t 1 = 1 := by
    rw [← hchi, h1Q, Units.val_one]
  refine ⟨htprod, ?_⟩
  have hres := om6m_orthResHom_tailDiag (b := b) (c := c) (t := t) (k := k) (g := gQ) hgdQ
  rw [h2Q] at hres
  refine LinearEquiv.ext fun a => ?_
  have hcongr := LinearEquiv.congr_fun hres.symm ((0 : Fin 0 ⊕ Fin 0 → K), a)
  rw [tailDiag_apply] at hcongr
  change (torusElt 0 K ![] (0 : Fin 0 ⊕ Fin 0 → K), k a) =
    ((0 : Fin 0 ⊕ Fin 0 → K), a) at hcongr
  exact (Prod.ext_iff.mp hcongr).2

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
