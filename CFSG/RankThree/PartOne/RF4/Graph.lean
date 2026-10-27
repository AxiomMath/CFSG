module

public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalRegularity
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups WithConv TensorProduct

open scoped CFSG.ConvolutionPoints


abbrev reeM (t : ReeTag) : ℕ := Fintype.card (Label t.tag)

@[expose] def reeLabelEquiv (t : ReeTag) : Label t.tag ≃ Fin (reeM t) :=
  Fintype.equivFin _

section Graph

variable (t : ReeTag) {L : Type} [Field L]

@[expose] def reeGraphHom (Φ : MulAut (adjointGroup t.tag L)) :
    adjointGroup t.tag L →* Matrix.GeneralLinearGroup (Fin (reeM t)) L :=
  (glReindex (reeLabelEquiv t)).toMonoidHom.comp
    ((modGLEquivGL t.tag L).toMonoidHom.comp ((adjointGroup t.tag L).subtype.comp Φ.toMonoidHom))

theorem reeGraphHom_apply (Φ : MulAut (adjointGroup t.tag L)) (g : adjointGroup t.tag L) :
    reeGraphHom t Φ g =
      glReindex (reeLabelEquiv t) (modGLEquivGL t.tag L ((Φ g : adjointGroup t.tag L) :
        ModGL t.tag L)) :=
  rfl

@[expose] def reeLetterCurveCo (l : Letter t.tag) (n : ℕ) :
    GLCoord L (Fin (reeM t)) →ₐ[L] Polynomial L :=
  (unitCo L (letterUnit t.tag (Polynomial L) l (Polynomial.X ^ n))).comp
    (glReindexCo (reeLabelEquiv t))

theorem toConv_aeval_comp_reeLetterCurveCo (l : Letter t.tag) (n : ℕ) (c : L) :
    toConv ((Polynomial.aeval c).comp (reeLetterCurveCo t l n)) =
      glPointEquiv (glReindex (reeLabelEquiv t)
        (modGLEquivGL t.tag L (letterUnit t.tag L l (c ^ n)))) := by
  have hb := baseChange_letterUnit ((Polynomial.aeval c : Polynomial L →ₐ[L] L) :
    Polynomial L →+* L) l (Polynomial.X ^ n)
  have h1 := comp_unitCo_of_baseChange (Polynomial.aeval c) _ _ hb
  rw [reeLetterCurveCo, ← AlgHom.comp_assoc, h1]
  apply glPointEquiv.symm.injective
  have hm : ∀ g : ModGL t.tag L, modGLPoint t.tag L g = glPointEquiv (modGLEquivGL t.tag L g) :=
    fun _ => rfl
  rw [glPointEquiv_symm_comp_glReindexCo, toConv_ofConv, MulEquiv.symm_apply_apply, hm,
    MulEquiv.symm_apply_apply]
  congr 2
  simp

variable {t}

theorem reeGraphHom_regular_x {Φ : MulAut (adjointGroup t.tag L)} (hΦ : IsReeExceptional t L Φ) :
    ∀ i, ∃ φ : GLCoord L (Fin (reeM t)) →ₐ[L] Polynomial L, ∀ c,
      toConv ((Polynomial.aeval c).comp φ) =
        glPointEquiv (reeGraphHom t Φ (adjX t.tag L i c)) := by
  intro i
  refine ⟨reeLetterCurveCo t (t.perm i, true) (t.exponent i), fun c => ?_⟩
  rw [toConv_aeval_comp_reeLetterCurveCo, reeGraphHom_apply]
  change _ = glPointEquiv (glReindex (reeLabelEquiv t) (modGLEquivGL t.tag L
    ((Φ (xElement i c) : adjointGroup t.tag L) : ModGL t.tag L)))
  rw [(hΦ i c).1]
  rfl

theorem reeGraphHom_regular_y {Φ : MulAut (adjointGroup t.tag L)} (hΦ : IsReeExceptional t L Φ) :
    ∀ i, ∃ φ : GLCoord L (Fin (reeM t)) →ₐ[L] Polynomial L, ∀ c,
      toConv ((Polynomial.aeval c).comp φ) =
        glPointEquiv (reeGraphHom t Φ (adjY t.tag L i c)) := by
  intro i
  refine ⟨reeLetterCurveCo t (t.perm i, false) (t.exponent i), fun c => ?_⟩
  rw [toConv_aeval_comp_reeLetterCurveCo, reeGraphHom_apply]
  change _ = glPointEquiv (glReindex (reeLabelEquiv t) (modGLEquivGL t.tag L
    ((Φ (yElement i c) : adjointGroup t.tag L) : ModGL t.tag L)))
  rw [(hΦ i c).2]
  rfl

end Graph

section QuotientPoints

variable {t : ReeTag} {L : Type} [Field L]

theorem tmul_one_mem_subgroupIdeal_graph (Φ : MulAut (adjointGroup t.tag L))
    {a : GLCoord L (Label t.tag)} (ha : a ∈ subgroupIdeal (adjointPointSubgroup t.tag L)) :
    a ⊗ₜ (1 : GLCoord L (Fin (reeM t))) ∈
      subgroupIdeal (graphPointSubgroup (reeGraphHom t Φ)) := by
  refine mem_pointsIdeal.2 fun y hy => ?_
  rw [subgroupPoints_map, transportPoints_graphSubgroup] at hy
  obtain ⟨g, rfl⟩ := hy
  rw [tensorPointEquiv_tmul, map_one, mul_one]
  refine mem_pointsIdeal.1 ha _ ((mem_subgroupPoints_adjointPointSubgroup t.tag L).2 ?_)
  rw [toConv_ofConv, MulEquiv.symm_apply_apply]
  exact g.2

variable (t L) in
abbrev reeGraphCoord (Φ : MulAut (adjointGroup t.tag L)) : Type :=
  GLCoord L (Label t.tag) ⊗[L] GLCoord L (Fin (reeM t)) ⧸
    subgroupIdeal (graphPointSubgroup (reeGraphHom t Φ))

variable [IsAlgClosed L]

theorem reeGraph_realization {Φ : MulAut (adjointGroup t.tag L)} (hΦ : IsReeExceptional t L Φ) :
    IsPointClosed L (graphPoints t.tag L (reeGraphHom t Φ)) ∧
      IsConnectedAlgebraicSubgroup L (graphPointSubgroup (reeGraphHom t Φ)) ∧
      Algebra.Smooth L (reeGraphCoord t L Φ) ∧
      IrreducibleSpace (PrimeSpectrum (reeGraphCoord t L Φ)) :=
  let h := (exceptional_Lang_exact_affine_group_realization L t.tag).2 (reeM t)
    (reeGraphHom t Φ) (reeGraphHom_regular_x hΦ) (reeGraphHom_regular_y hΦ)
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

@[expose] def reeGraphPointEquiv {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) :
    WithConv (reeGraphCoord t L Φ →ₐ[L] L) ≃* adjointGroup t.tag L :=
  (mapQuotientPointsEquiv (modGLPairPoint t.tag L (reeM t)) (graphSubgroup (reeGraphHom t Φ))
    (reeGraph_realization hΦ).2.1.pointsZero_eq).trans (graphSubgroupEquiv _).symm

theorem coe_reeGraphPointEquiv {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) (z : WithConv (reeGraphCoord t L Φ →ₐ[L] L)) :
    (reeGraphPointEquiv hΦ z : ModGL t.tag L) = (modGLPoint t.tag L).symm
      (toConv ((z.ofConv.comp (Ideal.Quotient.mkₐ L _)).comp
        Algebra.TensorProduct.includeLeft)) := by
  rw [reeGraphPointEquiv, MulEquiv.trans_apply, coe_graphSubgroupEquiv_symm,
    coe_mapQuotientPointsEquiv]
  rfl

@[expose] def reeGraphProjCo (Φ : MulAut (adjointGroup t.tag L)) :
    realizedCoord t.tag L →ₐc[L] reeGraphCoord t L Φ :=
  bialgHomQuotientLift (subgroupIdeal (adjointPointSubgroup t.tag L))
    ((Bialgebra.Quotient.mkBialgHom (subgroupIdeal (graphPointSubgroup (reeGraphHom t Φ)))).comp
      (includeLeftBialgHom L (GLCoord L (Label t.tag)) (GLCoord L (Fin (reeM t)))))
    (fun a ha => by
      rw [BialgHom.comp_apply, includeLeftBialgHom_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (tmul_one_mem_subgroupIdeal_graph Φ ha))

theorem reeGraphProjCo_mk (Φ : MulAut (adjointGroup t.tag L)) (a : GLCoord L (Label t.tag)) :
    reeGraphProjCo Φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (a ⊗ₜ 1) := by
  rw [reeGraphProjCo, bialgHomQuotientLift_mk, BialgHom.comp_apply, includeLeftBialgHom_apply]
  rfl

theorem reeGraphProjCo_comp_mkₐ (Φ : MulAut (adjointGroup t.tag L)) :
    (reeGraphProjCo Φ : realizedCoord t.tag L →ₐ[L] reeGraphCoord t L Φ).comp
        (Ideal.Quotient.mkₐ L _) =
      (Ideal.Quotient.mkₐ L _).comp Algebra.TensorProduct.includeLeft :=
  AlgHom.ext fun a => reeGraphProjCo_mk Φ a

theorem realizedPointEquiv_comp_reeGraphProjCo {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) (z : WithConv (reeGraphCoord t L Φ →ₐ[L] L)) :
    realizedPointEquiv t.tag L
        (toConv (z.ofConv.comp (reeGraphProjCo Φ : realizedCoord t.tag L →ₐ[L] _))) =
      reeGraphPointEquiv hΦ z := by
  apply Subtype.ext
  rw [coe_realizedPointEquiv, coe_reeGraphPointEquiv, ofConv_toConv, AlgHom.comp_assoc,
    reeGraphProjCo_comp_mkₐ, AlgHom.comp_assoc]

theorem bijective_reeGraphProjCo_points {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) :
    Function.Bijective fun z : WithConv (reeGraphCoord t L Φ →ₐ[L] L) =>
      toConv (z.ofConv.comp (reeGraphProjCo Φ : realizedCoord t.tag L →ₐ[L] _)) := by
  have h : (fun z : WithConv (reeGraphCoord t L Φ →ₐ[L] L) =>
      toConv (z.ofConv.comp (reeGraphProjCo Φ : realizedCoord t.tag L →ₐ[L] _))) =
      (realizedPointEquiv t.tag L).symm ∘ reeGraphPointEquiv hΦ := by
    funext z
    rw [Function.comp_apply, ← realizedPointEquiv_comp_reeGraphProjCo hΦ,
      MulEquiv.symm_apply_apply]
  rw [h]
  exact (realizedPointEquiv t.tag L).symm.bijective.comp (reeGraphPointEquiv hΦ).bijective

end QuotientPoints

end CFSG.RankThree.PartOne.RF4
