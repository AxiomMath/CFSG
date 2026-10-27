module

public import CFSG.RankThree.GF2n.Smith81.S81QGraphCl
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerMatrixSemilinearAction
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusModel
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin
open CFSG.RankThree.GF2n.Smith81.D6Spin (graphSpin)

private theorem w135c2_omfP8Aut_spinMatrix_injective {F : Type} [Field F] [CharP F 2] :
    Function.Injective (spinMatrix (quadPlus 4 F)) := by
  intro a b hab
  apply CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective (n := 4) (K := F)
  refine LinearEquiv.ext fun v => ?_
  rw [← spinMatrix_mulVec (quadPlus 4 F) a v, ← spinMatrix_mulVec (quadPlus 4 F) b v, hab]

private theorem w135c2_omfP8Aut_inner_case {F : Type} [Field F] [CharP F 2]
    {α θ : MulAut (spinGroup (quadPlus 4 F))}
    {A : GL (Fin 4 ⊕ Fin 4) F} {φ : F ≃+* F} (hφ : φ = RingEquiv.refl F)
    {h : spinGroup (quadPlus 4 F)} (hAeq : spinMatrix (quadPlus 4 F) h = A)
    (hmat : ∀ x, spinMatrix (quadPlus 4 F) ((θ * α * θ⁻¹) x) =
      A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
        (Fin 4 ⊕ Fin 4) φ (spinMatrix (quadPlus 4 F) x) * A⁻¹) :
    ∀ g, θ (α (θ.symm g)) = h * g * h⁻¹ := by
  intro g
  apply w135c2_omfP8Aut_spinMatrix_injective
  calc spinMatrix (quadPlus 4 F) (θ (α (θ.symm g)))
      = A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
            (Fin 4 ⊕ Fin 4) φ (spinMatrix (quadPlus 4 F) g) * A⁻¹ := by
          simpa only [MulAut.mul_apply, MulAut.inv_apply] using hmat g
    _ = A * spinMatrix (quadPlus 4 F) g * A⁻¹ := by
          rw [hφ, omPlusAut_glFieldEquiv_refl]
    _ = spinMatrix (quadPlus 4 F) (h * g * h⁻¹) := by
          rw [← hAeq, ← map_inv, ← map_mul, ← map_mul]

private theorem w135c2_omfP8Aut_graph_case {F : Type} [Field F] [CharP F 2]
    {α θ : MulAut (spinGroup (quadPlus 4 F))}
    {A : GL (Fin 4 ⊕ Fin 4) F} {φ : F ≃+* F} (hφ : φ = RingEquiv.refl F)
    {h : spinGroup (quadPlus 4 F)} (i₀ : Fin 4) {R : GL (Fin 4 ⊕ Fin 4) F}
    (hAeq : A = spinMatrix (quadPlus 4 F) h * R)
    (hRg : ∀ g, R * spinMatrix (quadPlus 4 F) g * R =
      spinMatrix (quadPlus 4 F) (graphSpin 4 F i₀ g))
    (hRinv : R⁻¹ = R)
    (hmat : ∀ x, spinMatrix (quadPlus 4 F) ((θ * α * θ⁻¹) x) =
      A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
        (Fin 4 ⊕ Fin 4) φ (spinMatrix (quadPlus 4 F) x) * A⁻¹) :
    ∀ g, θ (α (θ.symm g)) = h * graphSpin 4 F i₀ g * h⁻¹ := by
  intro g
  apply w135c2_omfP8Aut_spinMatrix_injective
  calc spinMatrix (quadPlus 4 F) (θ (α (θ.symm g)))
      = A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
            (Fin 4 ⊕ Fin 4) φ (spinMatrix (quadPlus 4 F) g) * A⁻¹ := by
          simpa only [MulAut.mul_apply, MulAut.inv_apply] using hmat g
    _ = A * spinMatrix (quadPlus 4 F) g * A⁻¹ := by
          rw [hφ, omPlusAut_glFieldEquiv_refl]
    _ = (spinMatrix (quadPlus 4 F) h * R) * spinMatrix (quadPlus 4 F) g *
          (spinMatrix (quadPlus 4 F) h * R)⁻¹ := by rw [hAeq]
    _ = spinMatrix (quadPlus 4 F) h * (R * spinMatrix (quadPlus 4 F) g * R) *
          (spinMatrix (quadPlus 4 F) h)⁻¹ := by
          rw [_root_.mul_inv_rev, hRinv]; group
    _ = spinMatrix (quadPlus 4 F) h * spinMatrix (quadPlus 4 F) (graphSpin 4 F i₀ g) *
          (spinMatrix (quadPlus 4 F) h)⁻¹ := by rw [hRg g]
    _ = spinMatrix (quadPlus 4 F) (h * graphSpin 4 F i₀ g * h⁻¹) := by
          conv_lhs => rw [← map_mul]
          conv_rhs => rw [map_mul, map_inv]

private theorem w135c2_omfP8Aut_glLin_mem_orthogonal {F : Type} [Field F] [CharP F 2]
    {A : GL (Fin 4 ⊕ Fin 4) F} {φ : F ≃+* F} (hφ : φ = RingEquiv.refl F) {μ : Fˣ}
    (hμ : (μ : F) = 1)
    (hsim : CFSG.StandardType.LieKnownR2.POmega.Inner.GGSemilinearSimilitude
      (quadPlus 4 F) A φ μ) :
    omPlusAutGlLin (Fin 4 ⊕ Fin 4) F A ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have h := hsim v
  rw [hφ] at h
  have hfun : (fun i => (RingEquiv.refl F) (v i)) = v := rfl
  rw [hfun, hμ, one_mul] at h
  simp only [RingEquiv.refl_apply] at h
  rw [omPlusAutGlLin_apply]
  exact h

theorem omPlus8_two_aut_inner_or_graph {F : Type} [Field F] (hF : Nat.card F = 2)
    (α : MulAut (spinGroup (quadPlus 4 F))) (hα : α * α = 1) :
    ∃ (θ : MulAut (spinGroup (quadPlus 4 F))) (h : spinGroup (quadPlus 4 F)),
      (∀ g, θ (α (θ.symm g)) = h * g * h⁻¹) ∨
        ∀ g, θ (α (θ.symm g)) = h * graphSpin 4 F ⟨3, by norm_num⟩ g * h⁻¹ := by
  have hFinite : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hFintype : Fintype F := Fintype.ofFinite F
  have hCharP : CharP F 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  obtain ⟨_, hμ1, hφr⟩ := omPlusAut_field_triv hF
  have hα2 : α ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, hα]
  obtain ⟨j, A, φ, μ, hsim, hmat⟩ :=
    CFSG.StandardType.LieKnownR2.POmega.Inner.exists_semilinear_similitude_of_triality_conj
      α 1 hα2
  let θ : MulAut (spinGroup (quadPlus 4 F)) :=
    (CFSG.StandardType.Triality.triSpinAut : MulAut (spinGroup (quadPlus 4 F))) ^ j
  have hφ : φ = RingEquiv.refl F := hφr φ
  have hμ : (μ : F) = 1 := hμ1 μ
  have hmatθ : ∀ x, spinMatrix (quadPlus 4 F) ((θ * α * θ⁻¹) x) =
      A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
        (Fin 4 ⊕ Fin 4) φ (spinMatrix (quadPlus 4 F) x) * A⁻¹ := fun x => hmat x
  set gA : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) :=
    omPlusAutGlLin (Fin 4 ⊕ Fin 4) F A with hgA
  have hA_orth : gA ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F) := by
    rw [hgA]
    exact w135c2_omfP8Aut_glLin_mem_orthogonal hφ hμ hsim
  by_cases hEven : Even (Module.finrank F
    (CFSG.RankThree.OrthogonalInvolutions.commSpace gA))
  · have hgAmem : gA ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadPlus 4 F)
        (nondegenerate_polarBilin_quadPlus 4 F) :=
      CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hA_orth, hEven⟩
    obtain ⟨h, hh⟩ :=
      CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus (n := 4)
        (by norm_num) hgAmem
    have hAeq : spinMatrix (quadPlus 4 F) h = A := by
      apply (omPlusAutGlLin (Fin 4 ⊕ Fin 4) F).injective
      rw [omPlusAutGlLin_spinMatrix, hh, hgA]
    exact ⟨θ, h, Or.inl (w135c2_omfP8Aut_inner_case hφ hAeq hmatθ)⟩
  · obtain ⟨h, R, hAeq, hRg, hRinv⟩ :=
      omPlusAut_graph_setup (n := 4) (by norm_num) hgA hA_orth
        (Nat.not_even_iff_odd.mp hEven) (⟨3, by norm_num⟩ : Fin 4)
    exact ⟨θ, h, Or.inr (w135c2_omfP8Aut_graph_case hφ (⟨3, by norm_num⟩ : Fin 4)
      hAeq hRg hRinv hmatθ)⟩

end CFSG.LocalAnalysis.WeakClosure81
