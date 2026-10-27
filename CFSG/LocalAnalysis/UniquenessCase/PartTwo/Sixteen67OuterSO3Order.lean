module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormSimilitude
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroProjective
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Orders
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Maximal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open Matrix CFSG.ComponentClassification

private lemma k67o_isoOrthGL_val {F : Type} [Field F] (hF : ringChar F ≠ 2)
    {R : GL (Fin 3) F} (hR : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R)
    (g : TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm R)) :
    (((Burgoyne.PSL.isoOrthGL hF R hR g : CatalogueBGraphForm.isometryGroup 3 F R) :
        GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      LinearMap.toMatrix' (g.val : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) := rfl

private lemma k67o_det_isoOrthGL {F : Type} [Field F] (hF : ringChar F ≠ 2)
    {R : GL (Fin 3) F} (hR : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R)
    (g : TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm R)) {c : F}
    (hact : ∀ v, g.val v = c • v) :
    (((Burgoyne.PSL.isoOrthGL hF R hR g : CatalogueBGraphForm.isometryGroup 3 F R) :
        GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = c ^ 3 := by
  rw [k67o_isoOrthGL_val hF hR g, LinearMap.det_toMatrix']
  have hgm : (g.val : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) = c • LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp [hact v]
  rw [hgm, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fin_fun]

theorem orderOf_le_card_add_one_of_isometry_three {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) {R : GL (Fin 3) F} (hR : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R)
    {X : GL (Fin 3) F}
    (hX : X ∈ CatalogueBGraphForm.isometryGroup 3 F R)
    (hdet : (X : Matrix (Fin 3) (Fin 3) F).det = 1) :
    orderOf X ≤ Nat.card F + 1 := by
  classical
  haveI : Finite (ProjGenLinGroup (Fin 2) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hodd : Odd (Nat.card F) :=
    CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two F hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hdim : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  set Q : QuadraticForm F (Fin 3 → F) :=
    CatalogueBLinearHigherB.matrixQuadraticForm R with hQdef
  have hQnd : Q.polarBilin.Nondegenerate := by
    rw [hQdef]
    exact CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hF R hR
  obtain ⟨d, psi, e, -, -, he'⟩ :=
    CatalogueBOrthogonalThreeSimilarity.finite_odd_orthogonal_three_trace_zero_similarity
      hodd Q hQnd hdim
  set Φ : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
      (ProjGenLinGroup (Fin 2) F × rootsOfUnity 2 F) :=
    e.trans (CatalogueBOrthogonal.traceZeroProjectiveEquiv h2).symm with hΦdef
  let π : TauCeti.QuadraticMap.orthogonalGroup Q →* ProjGenLinGroup (Fin 2) F :=
    (MonoidHom.fst _ _).comp Φ.toMonoidHom
  have hker : ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q, π g = 1 →
      ∃ ε : rootsOfUnity 2 F, ∀ v : Fin 3 → F, g.val v = (ε.val : F) • v := by
    intro g hg
    refine ⟨(Φ g).2, ?_⟩
    have hΦg : Φ g = (1, (Φ g).2) := Prod.ext hg rfl
    have heg : e g = CatalogueBOrthogonal.traceZeroProjectiveEquiv h2 (1, (Φ g).2) := by
      have h1 := congrArg (CatalogueBOrthogonal.traceZeroProjectiveEquiv h2) hΦg
      simp only [Φ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
      exact h1
    have hact : ∀ X : CatalogueBOrthogonal.traceZeroSubmodule F,
        (e g).val X = (((Φ g).2).val : F) • X := by
      intro X
      apply Subtype.ext
      rw [heg, ← ProjGenLinGroup.mk_one,
        CatalogueBOrthogonal.traceZeroProjectiveEquiv_val]
      simp
    intro v
    have h1 : (e.symm (e g)).val v = psi.symm ((e g).val (psi v)) := he' (e g) v
    rw [MulEquiv.symm_apply_apply] at h1
    rw [h1, hact (psi v), map_smul, LinearEquiv.symm_apply_apply]
  have hker_det : ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q, π g = 1 →
      (((Burgoyne.PSL.isoOrthGL hF R hR g :
          CatalogueBGraphForm.isometryGroup 3 F R) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).det = 1 → g = 1 := by
    intro g hg hgd
    obtain ⟨ε, hεv⟩ := hker g hg
    have hε2 : (ε.val : F) ^ 2 = 1 := (mem_rootsOfUnity' 2 ε.val).mp ε.property
    have hd3 : (ε.val : F) ^ 3 = 1 := by
      rw [← k67o_det_isoOrthGL hF hR g hεv]
      exact hgd
    have hcube : (ε.val : F) ^ 3 = (ε.val : F) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hε2, one_mul]
    rw [hcube] at hd3
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hεv v, hd3, one_smul]
    rfl
  set g₀ : TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Burgoyne.PSL.isoOrthGL hF R hR).symm ⟨X, hX⟩ with hg₀def
  have hg₀ : Burgoyne.PSL.isoOrthGL hF R hR g₀ =
      (⟨X, hX⟩ : CatalogueBGraphForm.isometryGroup 3 F R) :=
    (Burgoyne.PSL.isoOrthGL hF R hR).apply_symm_apply ⟨X, hX⟩
  let m : ℕ := orderOf (π g₀)
  have hpow : g₀ ^ m = 1 := by
    apply hker_det
    · rw [map_pow]
      exact pow_orderOf_eq_one (π g₀)
    · have h1 : Burgoyne.PSL.isoOrthGL hF R hR (g₀ ^ m) =
          (⟨X, hX⟩ : CatalogueBGraphForm.isometryGroup 3 F R) ^ m := by
        rw [map_pow, hg₀]
      rw [h1, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, Matrix.det_pow, hdet,
        one_pow]
  have hdvd : orderOf g₀ ∣ m := orderOf_dvd_of_pow_eq_one hpow
  have hordX : orderOf X = orderOf g₀ := by
    rw [← Subgroup.orderOf_mk X hX, ← hg₀]
    exact MulEquiv.orderOf_eq (Burgoyne.PSL.isoOrthGL hF R hR) g₀
  have hbd : orderOf (π g₀) ≤ Nat.card F + 1 :=
    CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le F (π g₀)
  have hpos : 0 < orderOf (π g₀) :=
    IsOfFinOrder.orderOf_pos (isOfFinOrder_of_finite (π g₀))
  calc orderOf X = orderOf g₀ := hordX
    _ ≤ orderOf (π g₀) := Nat.le_of_dvd hpos hdvd
    _ ≤ Nat.card F + 1 := hbd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
