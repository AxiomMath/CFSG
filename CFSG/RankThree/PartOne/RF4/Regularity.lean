module

public import CFSG.RankThree.PartOne.RF4.Projection
public import CFSG.LieType.AlgebraicGroups.RootCoordinateLang
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups WithConv TensorProduct

open scoped CFSG.ConvolutionPoints

variable {t : ReeTag} {L : Type} [Field L] [IsAlgClosed L]

@[expose] def reeGraphSndCoGL (Φ : MulAut (adjointGroup t.tag L)) :
    GLCoord L (Label t.tag) →ₐ[L] reeGraphCoord t L Φ :=
  ((Ideal.Quotient.mkₐ L _).comp Algebra.TensorProduct.includeRight).comp
    (glReindexCo (reeLabelEquiv t).symm)

theorem toConv_comp_reeGraphSndCoGL {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) (w : reeGraphCoord t L Φ →ₐ[L] L) :
    toConv (w.comp (reeGraphSndCoGL Φ)) =
      modGLPoint t.tag L (Φ (reeGraphPointEquiv hΦ (toConv w))) := by
  have h2 : glPointEquiv.symm (toConv ((w.comp (Ideal.Quotient.mkₐ L _)).comp
      Algebra.TensorProduct.includeRight)) =
        reeGraphHom t Φ (reeGraphPointEquiv hΦ (toConv w)) :=
    congrArg Prod.snd (modGLPairPoint_symm_reeGraph hΦ (toConv w))
  have hm : ∀ g : ModGL t.tag L,
      modGLPoint t.tag L g = glPointEquiv (modGLEquivGL t.tag L g) := fun _ => rfl
  apply glPointEquiv.symm.injective
  rw [reeGraphSndCoGL, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    glPointEquiv_symm_comp_glReindexCo, h2, reeGraphHom_apply, glReindex_symm_glReindex, hm,
    MulEquiv.symm_apply_apply]

theorem comp_reeGraphSndCoGL_mem {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) (w : reeGraphCoord t L Φ →ₐ[L] L) :
    w.comp (reeGraphSndCoGL Φ) ∈ subgroupPoints (adjointPointSubgroup t.tag L) := by
  rw [mem_subgroupPoints_adjointPointSubgroup, toConv_comp_reeGraphSndCoGL hΦ,
    MulEquiv.symm_apply_apply]
  exact (Φ _).2

@[expose] def reeGraphSndCo0 {Φ : MulAut (adjointGroup t.tag L)} (hΦ : IsReeExceptional t L Φ) :
    realizedCoord t.tag L →ₐ[L] reeGraphCoord t L Φ :=
  haveI := (reeGraph_realization hΦ).2.1.finiteType
  haveI := (reeGraph_realization hΦ).2.1.isReduced
  liftOfPoints _ (reeGraphSndCoGL Φ) (comp_reeGraphSndCoGL_mem hΦ)

theorem realizedPointEquiv_comp_reeGraphSndCo0 {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) (w : WithConv (reeGraphCoord t L Φ →ₐ[L] L)) :
    realizedPointEquiv t.tag L (toConv (w.ofConv.comp (reeGraphSndCo0 hΦ))) =
      Φ (reeGraphPointEquiv hΦ w) := by
  have := (reeGraph_realization hΦ).2.1.finiteType
  have := (reeGraph_realization hΦ).2.1.isReduced
  have h : (reeGraphSndCo0 hΦ).comp (Ideal.Quotient.mkₐ L _) = reeGraphSndCoGL Φ :=
    liftOfPoints_comp_mkₐ _ _ _
  apply Subtype.ext
  rw [coe_realizedPointEquiv, ofConv_toConv, AlgHom.comp_assoc, h,
    toConv_comp_reeGraphSndCoGL hΦ, toConv_ofConv, MulEquiv.symm_apply_apply]

@[expose] def reeGraphSndCo {Φ : MulAut (adjointGroup t.tag L)} (hΦ : IsReeExceptional t L Φ) :
    realizedCoord t.tag L →ₐc[L] reeGraphCoord t L Φ :=
  haveI := (reeGraph_realization hΦ).2.1.finiteType
  haveI := (reeGraph_realization hΦ).2.1.isReduced
  bialgHomOfPointMulTo (reeGraphSndCo0 hΦ) fun y z => by
    apply (realizedPointEquiv t.tag L).injective
    rw [map_mul, realizedPointEquiv_comp_reeGraphSndCo0, realizedPointEquiv_comp_reeGraphSndCo0,
      realizedPointEquiv_comp_reeGraphSndCo0, map_mul, map_mul]

theorem realizedPointEquiv_comp_reeGraphSndCo {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) (w : WithConv (reeGraphCoord t L Φ →ₐ[L] L)) :
    realizedPointEquiv t.tag L
        (toConv (w.ofConv.comp (reeGraphSndCo hΦ : realizedCoord t.tag L →ₐ[L] _))) =
      Φ (reeGraphPointEquiv hΦ w) :=
  realizedPointEquiv_comp_reeGraphSndCo0 hΦ w

theorem exceptional_Lang_ree_map_regularity [CharP L t.prime]
    {Φ : MulAut (adjointGroup t.tag L)} (hΦ : IsReeExceptional t L Φ)
    (hli : LinearIndependent L (Sum.elim (fun α : {α // IsRoot t.tag α} => pinnedE t.tag L α.1)
      (tangentH t.tag L))) :
    ∃ σ : realizedCoord t.tag L →ₐc[L] realizedCoord t.tag L,
      (∀ φ, realizedPointEquiv t.tag L (pointMap σ φ) =
        Φ (realizedPointEquiv t.tag L φ)) ∧
      (∀ σ' : realizedCoord t.tag L →ₐc[L] realizedCoord t.tag L,
        (∀ φ, realizedPointEquiv t.tag L (pointMap σ' φ) =
          Φ (realizedPointEquiv t.tag L φ)) → σ' = σ) ∧
      (∃ Fr : realizedCoord t.tag L →ₐc[L] realizedCoord t.tag L,
        ∀ φ, (realizedPointEquiv t.tag L (pointMap Fr φ) : ModGL t.tag L) =
          Units.map (entrywiseHom (iterateFrobenius L t.prime 1))
            (realizedPointEquiv t.tag L φ)) ∧
      ∀ Fr : realizedCoord t.tag L →ₐc[L] realizedCoord t.tag L,
        (∀ φ, (realizedPointEquiv t.tag L (pointMap Fr φ) : ModGL t.tag L) =
          Units.map (entrywiseHom (iterateFrobenius L t.prime 1))
            (realizedPointEquiv t.tag L φ)) →
        σ * σ = Fr ∧ σ * Fr = Fr * σ ∧
        ∀ a : ℕ, (Fr ^ a * σ) * (Fr ^ a * σ) = Fr ^ (2 * a + 1) ∧
          ∀ D ∈ tangentSpace L (realizedCoord t.tag L) (Bialgebra.counitAlgHom L _),
            D ∘ₗ (((Fr ^ a * σ) * (Fr ^ a * σ) : realizedCoord t.tag L →ₐc[L] _) :
              realizedCoord t.tag L →ₐ[L] realizedCoord t.tag L).toLinearMap = 0 := by
  have hG := isConnectedAlgebraicSubgroup_adjointPointSubgroup t.tag L
  have hΓ := reeGraph_realization hΦ
  have := hG.finiteType
  have := hΓ.2.1.finiteType
  have := hΓ.2.2.1
  obtain ⟨ψ, hψ, -⟩ := exceptional_Lang_bijective_tangent_group_map_isomorphism
    (reeGraphProjCo Φ) (bijective_reeGraphProjCo_points hΦ) (reeGraph_tangent_bijective hΦ hli)
  have hdet : ∀ σ₁ σ₂ : realizedCoord t.tag L →ₐc[L] realizedCoord t.tag L,
      (∀ φ, realizedPointEquiv t.tag L (pointMap σ₁ φ) =
        realizedPointEquiv t.tag L (pointMap σ₂ φ)) → σ₁ = σ₂ := by
    intro σ₁ σ₂ h
    have h' : (σ₁ : realizedCoord t.tag L →ₐ[L] realizedCoord t.tag L) = σ₂ :=
      (exceptional_Lang_affine_point_and_product_geometry L).2.2.2.2.1 _ _ _ _ fun x =>
        congrArg ofConv ((realizedPointEquiv t.tag L).injective (h (toConv x)))
    exact BialgHom.ext fun x => DFunLike.congr_fun h' x
  have hσ : ∀ φ, realizedPointEquiv t.tag L (pointMap (ψ.comp (reeGraphSndCo hΦ)) φ) =
      Φ (realizedPointEquiv t.tag L φ) := by
    intro φ
    have hw : reeGraphPointEquiv hΦ
        (toConv (φ.ofConv.comp (ψ : reeGraphCoord t L Φ →ₐ[L] _))) =
        realizedPointEquiv t.tag L φ := by
      rw [← realizedPointEquiv_comp_reeGraphProjCo hΦ, ofConv_toConv]
      congr 2
      exact AlgHom.ext fun x => congrArg φ.ofConv (DFunLike.congr_fun hψ x)
    rw [← hw, ← realizedPointEquiv_comp_reeGraphSndCo hΦ, ofConv_toConv]
    rfl
  obtain ⟨σF, hσF, hdF, -⟩ :=
    (exceptional_Lang_ordinary_Frobenius_diagram_morphisms t.prime L).1 t.tag 1 le_rfl
  refine ⟨ψ.comp (reeGraphSndCo hΦ), hσ, fun σ' h => hdet _ _ fun φ => (h φ).trans (hσ φ).symm,
    ⟨σF, hσF⟩, fun Fr hFr => ?_⟩
  set σ := ψ.comp (reeGraphSndCo hΦ)
  have hFr' : ∀ φ, realizedPointEquiv t.tag L (pointMap Fr φ) =
      frobeniusTwist t.tag L (iterateFrobenius L t.prime 1) (realizedPointEquiv t.tag L φ) :=
    fun φ => Subtype.ext (hFr φ)
  have hFrF : Fr = σF := hdet _ _ fun φ => Subtype.ext ((hFr φ).trans (hσF φ).symm)
  have hsq : σ * σ = Fr := hdet _ _ fun φ => by
    rw [pointMap_mul, hσ, hσ, hFr']
    exact DFunLike.congr_fun hΦ.comp_self _
  have hcomm : σ * Fr = Fr * σ := hdet _ _ fun φ => by
    rw [pointMap_mul, pointMap_mul, hFr', hσ, hσ, hFr']
    exact (DFunLike.congr_fun hΦ.comm_frobenius _).symm
  have hpow : ∀ a : ℕ, (Fr ^ a * σ) * (Fr ^ a * σ) = Fr ^ (2 * a + 1) := fun a => by
    have hc : σ * Fr ^ a = Fr ^ a * σ := (Commute.pow_right hcomm a).eq
    calc (Fr ^ a * σ) * (Fr ^ a * σ) = Fr ^ a * (σ * Fr ^ a) * σ := by
          simp only [mul_assoc]
      _ = Fr ^ a * (Fr ^ a * σ) * σ := by rw [hc]
      _ = Fr ^ (a + a) * (σ * σ) := by rw [pow_add]; simp only [mul_assoc]
      _ = Fr ^ (2 * a + 1) := by rw [hsq, ← pow_succ, two_mul]
  refine ⟨hsq, hcomm, fun a => ⟨hpow a, fun D hD => ?_⟩⟩
  rw [hpow, pow_succ', hFrF]
  change D ∘ₗ ((σF : realizedCoord t.tag L →ₐ[L] _).comp
    ((σF ^ (2 * a) : realizedCoord t.tag L →ₐc[L] _) :
      realizedCoord t.tag L →ₐ[L] _)).toLinearMap = 0
  rw [AlgHom.comp_toLinearMap, ← LinearMap.comp_assoc, hdF D hD, LinearMap.zero_comp]

theorem realizedPointEquiv_pointMap_pow' (τ : Tag)
    (Frc : realizedCoord τ L →ₐc[L] realizedCoord τ L) (Fr : MulAut (adjointGroup τ L))
    (hFrc : ∀ φ, realizedPointEquiv τ L (pointMap Frc φ) = Fr (realizedPointEquiv τ L φ))
    (a : ℕ) (φ : WithConv (realizedCoord τ L →ₐ[L] L)) :
    realizedPointEquiv τ L (pointMap (Frc ^ a) φ) = (Fr ^ a) (realizedPointEquiv τ L φ) := by
  induction a generalizing φ with
  | zero => rfl
  | succ a ih =>
    rw [pow_succ, pointMap_mul, hFrc, ih, pow_succ', MulAut.mul_apply]

theorem ree_lang_exceptional [CharP L t.prime] {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ)
    (hli : LinearIndependent L (Sum.elim (fun α : {α // IsRoot t.tag α} => pinnedE t.tag L α.1)
      (tangentH t.tag L)))
    (Fr : MulAut (adjointGroup t.tag L))
    (hFr : ∀ g, (Fr g : ModGL t.tag L) =
      Units.map (entrywiseHom (iterateFrobenius L t.prime 1)) (g : ModGL t.tag L))
    (a : ℕ) (x : adjointGroup t.tag L) : ∃ h, x = h⁻¹ * (Φ * Fr ^ a) h := by
  obtain ⟨σ, hσ, -, ⟨Frc, hFrc⟩, hall⟩ := exceptional_Lang_ree_map_regularity hΦ hli
  obtain ⟨-, -, hpow⟩ := hall Frc hFrc
  obtain ⟨-, hD⟩ := hpow a
  have hFrc' : ∀ φ, realizedPointEquiv t.tag L (pointMap Frc φ) =
      Fr (realizedPointEquiv t.tag L φ) := fun φ => Subtype.ext (by rw [hFrc, hFr])
  obtain ⟨h, hh⟩ := exceptional_Lang_connected_twisted_orbit_surjectivity (Frc ^ a * σ)
    (m := 2) (by norm_num) (fun D hDT => by rw [sq]; exact hD D hDT)
    ((realizedPointEquiv t.tag L).symm x)
  refine ⟨realizedPointEquiv t.tag L h, ?_⟩
  have hx := congrArg (realizedPointEquiv t.tag L) hh
  rw [MulEquiv.apply_symm_apply, map_mul, map_inv] at hx
  rw [hx, pointMap_mul, hσ, realizedPointEquiv_pointMap_pow' t.tag Frc Fr hFrc', MulAut.mul_apply]

end CFSG.RankThree.PartOne.RF4
