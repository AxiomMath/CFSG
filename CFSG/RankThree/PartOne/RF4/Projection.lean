module

public import CFSG.RankThree.PartOne.RF4.Bound
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups WithConv TensorProduct Module

open scoped CFSG.ConvolutionPoints

variable {t : ReeTag} {L : Type} [Field L] [IsAlgClosed L]

theorem modGLPairPoint_symm_reeGraph {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) (z : WithConv (reeGraphCoord t L Φ →ₐ[L] L)) :
    (modGLPairPoint t.tag L (reeM t)).symm
        (toConv (z.ofConv.comp (Ideal.Quotient.mkₐ L _))) =
      ((reeGraphPointEquiv hΦ z : ModGL t.tag L),
        reeGraphHom t Φ (reeGraphPointEquiv hΦ z)) := by
  rw [← coe_mapQuotientPointsEquiv (modGLPairPoint t.tag L (reeM t))
    (graphSubgroup (reeGraphHom t Φ)) (reeGraph_realization hΦ).2.1.pointsZero_eq z]
  conv_lhs => rw [← (graphSubgroupEquiv (reeGraphHom t Φ)).apply_symm_apply
    (mapQuotientPointsEquiv _ _ (reeGraph_realization hΦ).2.1.pointsZero_eq z)]
  rfl

theorem exists_linearIndependent_reeGraphProj {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ)
    (hli : LinearIndependent L (Sum.elim (fun α : {α // IsRoot t.tag α} => pinnedE t.tag L α.1)
      (tangentH t.tag L))) :
    ∃ v : {α // IsRoot t.tag α} ⊕ Fin t.tag.rank →
        TangentSpace L (reeGraphCoord t L Φ) (Bialgebra.counitAlgHom L _),
      LinearIndependent L (tangentMap
        (reeGraphProjCo Φ : realizedCoord t.tag L →ₐ[L] _)
        (BialgHom.counitAlgHom_comp (reeGraphProjCo Φ)) ∘ v) := by
  choose φx hφx using reeGraphHom_regular_x hΦ
  choose φy hφy using reeGraphHom_regular_y hΦ
  let v : {α // IsRoot t.tag α} ⊕ Fin t.tag.rank →
      TangentSpace L (reeGraphCoord t L Φ) (Bialgebra.counitAlgHom L _) :=
    Sum.elim (fun α => ⟨_, pinnedCurve_mem φx φy (reeGraphHom t Φ) hφx hφy α.1⟩)
      (fun i => ⟨_, torusCurve_mem φx φy (reeGraphHom t Φ) hφx hφy i⟩)
  refine ⟨v, LinearIndependent.of_comp (tangentEntries _) ?_⟩
  have hli' := hli.map'
    (LinearMap.toMatrixAlgEquiv (Finsupp.basisSingleOne (R := L)
      (ι := Label t.tag))).toLinearEquiv.toLinearMap (LinearEquiv.ker _)
  convert hli' using 1
  funext x
  ext a b
  rcases x with α | i
  · show dualTangent ((Polynomial.aeval (DualNumber.eps : DualNumber L)).comp
        (graphCurveCo φx φy (reeGraphHom t Φ) hφx hφy
          (pinnedWord t.tag (Polynomial L) α.1 Polynomial.X)))
        (reeGraphProjCo Φ (Ideal.Quotient.mk _ (glEntry L (Label t.tag) a b))) =
      endMatrix t.tag (pinnedE t.tag L α.1) a b
    rw [reeGraphProjCo_mk, pinnedCurve_mk, endMatrix_apply]
  · show dualTangent ((torusDualPoint L).comp (graphCurveCo φx φy (reeGraphHom t Φ) hφx hφy
        (torusWord t.tag (TorusAffine L 1 0) i (torusUnit L 1 0 0))))
        (reeGraphProjCo Φ (Ideal.Quotient.mk _ (glEntry L (Label t.tag) a b))) =
      endMatrix t.tag (tangentH t.tag L i) a b
    rw [reeGraphProjCo_mk, torusCurve_mk, endMatrix_apply]

theorem reeGraph_tangent_bijective {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ)
    (hli : LinearIndependent L (Sum.elim (fun α : {α // IsRoot t.tag α} => pinnedE t.tag L α.1)
      (tangentH t.tag L))) :
    Function.Bijective (tangentMap
      (reeGraphProjCo Φ : realizedCoord t.tag L →ₐ[L] reeGraphCoord t L Φ)
      (BialgHom.counitAlgHom_comp (reeGraphProjCo Φ))) := by
  have hG := (exceptional_Lang_exact_affine_group_realization L t.tag).1
  have hΓ := reeGraph_realization hΦ
  have := hG.2.1.finiteType
  have := hΓ.2.1.finiteType
  have : FiniteDimensional L
      (TangentSpace L (realizedCoord t.tag L) (Bialgebra.counitAlgHom L _)) :=
    finiteDimensional_tangentSpace _
  have : FiniteDimensional L
      (TangentSpace L (reeGraphCoord t L Φ) (Bialgebra.counitAlgHom L _)) :=
    finiteDimensional_tangentSpace _
  have hcard : Fintype.card ({α // IsRoot t.tag α} ⊕ Fin t.tag.rank) = reeM t :=
    Fintype.card_congr (Equiv.sumComm _ _)
  obtain ⟨v, hv⟩ := exists_linearIndependent_reeGraphProj hΦ hli
  exact (bijective_of_linearIndependent_comp (finrank_tangentSpace_reeGraphCoord_le hΦ _)
    (finrank_tangentSpace_realizedCoord_le _) _ hcard hv).1

end CFSG.RankThree.PartOne.RF4
