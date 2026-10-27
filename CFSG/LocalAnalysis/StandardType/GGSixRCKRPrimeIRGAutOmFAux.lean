module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTrialityAut
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightAutNormal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTrialityFamily
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourGlobal

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.SeitzReduction.OmegaPilot
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped Pointwise

abbrev irgOF_F (g : ℕ) : Type := GaloisField 2 g

abbrev irgOF_K (g : ℕ) : Type := spinGroup (Spin.quadPlus 4 (irgOF_F g))

abbrev irgOF_P (g : ℕ) : Type :=
  matrixProjectiveDerived (coordinateQuadPlus 4 (irgOF_F g))

theorem irgOF_center_eq_bot
    (g : ℕ) :
    Subgroup.center (ggU .POmegaPlus 4 g).K = ⊥ := by
  dsimp [ggU, LieType.Universal.lieUniversal]
  exact CFSG.SeitzReduction.OmegaPilot.center_spinGroup_quadPlus_eq_bot'
    CFSG.SeitzReduction.OmegaPilot.d4_three_le

noncomputable def irgOF_quotBotEquiv
    (g : ℕ) :
    IRGQuot .POmegaPlus 4 g ≃* irgOF_K g := by
  have hc := irgOF_center_eq_bot (g := g)
  exact (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot

noncomputable def irgOF_quotEquiv
    (g : ℕ) :
    IRGQuot .POmegaPlus 4 g ≃* irgOF_P g :=
  (irgOF_quotBotEquiv (g := g)).trans (spin8Equiv (irgOF_F g))

theorem irgOF_quotEquiv_mk
    (g : ℕ)
    (x : (ggU .POmegaPlus 4 g).K) :
    irgOF_quotEquiv (g := g)
      (QuotientGroup.mk' (Subgroup.center (ggU .POmegaPlus 4 g).K) x) =
      spin8Equiv (irgOF_F g) x := by
  rw [irgOF_quotEquiv, irgOF_quotBotEquiv]
  change spin8Equiv (irgOF_F g)
    ((QuotientGroup.quotientMulEquivOfEq (irgOF_center_eq_bot g)).trans
      QuotientGroup.quotientBot (↑x)) = _
  rw [MulEquiv.trans_apply]
  change spin8Equiv (irgOF_F g)
    (QuotientGroup.quotientBot ((QuotientGroup.quotientMulEquivOfEq (irgOF_center_eq_bot g)) ↑x)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem irgOF_normalForm
    (g : ℕ) (α : MulAut (irgOF_P g)) :
    ∃ (x : irgOF_P g) (ρ : d4DiagramGroup) (σ : irgOF_F g ≃+* irgOF_F g),
      α = MulAut.conj x * plusFourGraphAut (irgOF_F g) ρ * fieldAutHom (irgOF_F g) 4 σ := by
  have hτ3 : (plusFourTriality (irgOF_F g)) ^ 3 = 1 := plusFourTriality_pow_three
  have hτx : plusFourTriality (irgOF_F g) •
      projectivePointFamily (coordinateQuadPlus 4 (irgOF_F g)) ≠
      projectivePointFamily (coordinateQuadPlus 4 (irgOF_F g)) :=
    plusFourTriality_smul_pointFamily_ne
  have hτs : ∀ σ : irgOF_F g ≃+* irgOF_F g,
      plusFourTriality (irgOF_F g) * fieldAutHom (irgOF_F g) 4 σ =
        fieldAutHom (irgOF_F g) 4 σ * plusFourTriality (irgOF_F g) :=
    plusFourTriality_mul_fieldAutHom
  have hκτ : symmetryAut (coordinateQuadPlus 4 (irgOF_F g)) (lastPlaneVec 3) *
      plusFourTriality (irgOF_F g) *
      (symmetryAut (coordinateQuadPlus 4 (irgOF_F g)) (lastPlaneVec 3))⁻¹ =
      (plusFourTriality (irgOF_F g))⁻¹ :=
    symmetryAut_conj_plusFourTriality
  obtain ⟨Φ, -, -, hgen, hα⟩ :=
    normalForm_four_of_triality hτ3 hτx hτs hκτ
  obtain ⟨x, π, hπ, σ, hα'⟩ := hα α
  have hτrange : plusFourTriality (irgOF_F g) ∈ (plusFourGraphAut (irgOF_F g)).range :=
    ⟨d4TrialitySym, rfl⟩
  have hκrange : symmetryAut (coordinateQuadPlus 4 (irgOF_F g)) (lastPlaneVec 3) ∈
      (plusFourGraphAut (irgOF_F g)).range := by
    rw [symmetryAut_eq_plusFourGraphAut_d4ForkSym]
    exact ⟨d4ForkSym, rfl⟩
  have hclosure : Subgroup.closure ({plusFourTriality (irgOF_F g),
      symmetryAut (coordinateQuadPlus 4 (irgOF_F g)) (lastPlaneVec 3)} :
        Set (MulAut (irgOF_P g))) ≤ (plusFourGraphAut (irgOF_F g)).range :=
    (Subgroup.closure_le (plusFourGraphAut (irgOF_F g)).range).mpr (by
      intro z hz
      rcases hz with rfl | rfl
      · exact hτrange
      · exact hκrange)
  obtain ⟨ρ, hρ⟩ := hclosure hπ
  exact ⟨x, ρ, σ, by rw [hα', hρ]⟩

end CFSG.StandardType.RCKRP
