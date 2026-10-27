module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRepMain
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix

namespace SLRep

variable {G : Type} [Group G] {m : ℕ} {F : Type} [Field F]

theorem exists_toGL_eq_inv_mul_diagGL (P : GL (Fin (m + 1)) F) :
    ∃ (A₀ : SpecialLinearGroup (Fin (m + 1)) F) (d : Fin (m + 1) → Fˣ),
      SpecialLinearGroup.toGL A₀ = P⁻¹ * InnerDiagA.diagGL d := by
  set d : Fin (m + 1) → Fˣ := Pi.mulSingle 0 (GeneralLinearGroup.det P) with hd
  have hdet : ((P⁻¹ * InnerDiagA.diagGL d : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 := by
    have h1 : (GeneralLinearGroup.det (InnerDiagA.diagGL d) : F) =
        (GeneralLinearGroup.det P : F) := by
      rw [GeneralLinearGroup.val_det_apply, InnerDiagA.coe_diagGL, det_diagonal, ← Units.coe_prod,
        hd, Finset.prod_pi_mulSingle', ite_eq_left (Finset.mem_univ _)]
    have h2 : GeneralLinearGroup.det (P⁻¹ * InnerDiagA.diagGL d) = 1 := by
      rw [map_mul, map_inv, Units.ext h1, inv_mul_cancel]
    have h3 := congrArg (fun u : Fˣ => (u : F)) h2
    simpa only [GeneralLinearGroup.val_det_apply, Units.val_one] using h3
  exact ⟨⟨_, hdet⟩, d, Units.ext rfl⟩

theorem ggFrameDiag_ggFrame_of_conj {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G} {b : G}
    {A P : GL (Fin (m + 1)) F} (hb : ∀ u, b * ψ u * b⁻¹ = ψ (InnerDiagA.conjSL A u))
    (hP : ((P * A * P⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag)
    {A₀ : SpecialLinearGroup (Fin (m + 1)) F} {d : Fin (m + 1) → Fˣ}
    (hA₀ : SpecialLinearGroup.toGL A₀ = P⁻¹ * InnerDiagA.diagGL d) :
    GGFrameDiag (ggFrame ψ A₀) b := by
  generalize hDdef : P * A * P⁻¹ = D at hP
  have hDt : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal (Matrix.diag (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) :=
    hP.diagonal_diag.symm
  have hED : InnerDiagA.diagGL d * D = D * InnerDiagA.diagGL d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL, hDt, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hQD : P⁻¹ * InnerDiagA.diagGL d * D = A * (P⁻¹ * InnerDiagA.diagGL d) := by
    calc P⁻¹ * InnerDiagA.diagGL d * D = P⁻¹ * (InnerDiagA.diagGL d * D) := by group
      _ = P⁻¹ * (D * InnerDiagA.diagGL d) := by rw [hED]
      _ = A * (P⁻¹ * InnerDiagA.diagGL d) := by rw [← hDdef]; group
  refine ⟨D, _, hDt, fun s => ?_⟩
  rw [ggFrame_apply, ggFrame_apply, hb]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [RootPlaneA.toGL_conjSL, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hA₀,
    ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  calc A * (P⁻¹ * InnerDiagA.diagGL d * SpecialLinearGroup.toGL s *
        (P⁻¹ * InnerDiagA.diagGL d)⁻¹) * A⁻¹ =
      A * (P⁻¹ * InnerDiagA.diagGL d) * SpecialLinearGroup.toGL s *
        (A * (P⁻¹ * InnerDiagA.diagGL d))⁻¹ := by group
    _ = P⁻¹ * InnerDiagA.diagGL d * D * SpecialLinearGroup.toGL s *
        (P⁻¹ * InnerDiagA.diagGL d * D)⁻¹ := by rw [hQD]
    _ = P⁻¹ * InnerDiagA.diagGL d * (D * SpecialLinearGroup.toGL s * D⁻¹) *
        (P⁻¹ * InnerDiagA.diagGL d)⁻¹ := by group

end SLRep

section Inputs

theorem ggSLBstarFrameInput_holds : GGSLBstarFrameInput := by
  intro G _ _ p B Bs x L D J m f ψ hctx s1 hpq
  obtain ⟨P, hP⟩ := ggBstarToralPSLInput_holds G p B Bs x L D J m f ψ hctx s1.1 hpq
  obtain ⟨A₀, d, hA₀⟩ := SLRep.exists_toGL_eq_inv_mul_diagGL P
  refine ⟨A₀, fun b hb => ?_⟩
  have hb' : b⁻¹ ∈ Bs := Bs.inv_mem hb
  obtain ⟨A, hA⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hctx.2.2.2.1.2 hctx.2.2.2.2.1.2
    (hctx.2.2.2.2.2.2.1.2 b⁻¹ hb')
  refine SLRep.ggFrameDiag_ggFrame_of_conj (fun u => ?_) (hP b⁻¹ hb' A hA) hA₀
  have h := hA u
  rw [inv_inv] at h
  exact h

theorem ggSixRootFusionSLRepInput_of_nonsplit_residual
    (hN : GGSixRootFusionSLRepNonsplitInput) (hR : GGSixRootFusionSLRepResidualInput) :
    GGSixRootFusionSLRepInput :=
  ggSixRootFusionSLRepInput_of_frame ggSLBstarFrameInput_holds hN hR

end Inputs

end CFSG.StandardType
