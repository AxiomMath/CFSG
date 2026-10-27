module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepToral

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

namespace UFusion

open InnerDiagSU

variable {G : Type} [Group G] {m f : ℕ} {F : Type} [Field F] [Finite F] [Fact (Nat.Prime 2)]
  [CharP F 2]

omit [Finite F] [Fact (Nat.Prime 2)] [CharP F 2] in
theorem diagHom_eq_diagGL (τ : Fin (m + 1) → Fˣ) :
    diagHom (m + 1) τ = InnerDiagA.diagGL (F := F) τ :=
  Units.ext (by rw [coe_diagHom, InnerDiagA.coe_diagGL])

theorem norm_one_of_pow {τ : Fˣ} (hτ : (τ : F) ^ (2 ^ f + 1) = 1) :
    unitaryInvolution F 2 f (τ : F) * τ = 1 := by
  rw [unitaryInvolution_apply, ← pow_succ]
  exact hτ

theorem mem_uFrameTorus_of_frameDiagU (hF : Nat.card F = (2 ^ f) ^ 2)
    {ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G} {P : GL (Fin (m + 1)) F}
    (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (P : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = antidiag (m + 1)) {b : G}
    (hb : SURep.GGFrameDiagU (SURep.ggFrameU hF ψ P hP) b) : b ∈ uFrameTorus ψ P := by
  obtain ⟨τ, hτ, hact⟩ := hb
  have hA : IsJUnitary (unitaryInvolution F 2 f) (LinFusion.ggFrameDiag P τ) :=
    isJUnitary_frame hP (isIdUnitary_diagGL fun i => norm_one_of_pow (hτ i))
  refine ⟨τ, hA, fun u => ?_⟩
  have hs : ∀ v : SU (unitaryInvolution F 2 f) (m + 1),
      ((SURep.ggFrameEquiv hF P hP v :
        ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F (m + 1))) : GL (Fin (m + 1)) F) =
        P * (v : GL (Fin (m + 1)) F) * P⁻¹ := by
    intro v
    have h1 := SURep.coe_ggFrameEquiv_symm hF P hP (SURep.ggFrameEquiv hF P hP v)
    rw [MulEquiv.symm_apply_apply] at h1
    rw [h1]
    group
  have hφ : ∀ v : SU (unitaryInvolution F 2 f) (m + 1),
      SURep.ggFrameU hF ψ P hP (SURep.ggFrameEquiv hF P hP v) = ψ v := by
    intro v
    rw [SURep.ggFrameU_apply, MulEquiv.symm_apply_apply]
  have h1 := hact (SURep.ggFrameEquiv hF P hP u)
    (SURep.ggFrameEquiv hF P hP (conjSU (LinFusion.ggFrameDiag P τ) hA u)) (by
      rw [hs, hs, coe_conjSU, LinFusion.ggFrameDiag, diagHom_eq_diagGL]
      group)
  rwa [hφ, hφ] at h1

end UFusion

section Inputs

theorem ggUnitaryBstarFrameInput_holds : GGUnitaryBstarFrameInput := by
  intro G _ _ p B Bs x L D J m f hf ψ hctx s1 hp
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨P, hP, hB⟩ := ggSUBstarFrameInput_holds G p B Bs x L D J (m + 1) f ψ hctx s1 hp
  exact ⟨P, hP, fun b hb => UFusion.mem_uFrameTorus_of_frameDiagU _ hP (hB b hb)⟩

theorem ggStepTwoUnitaryFusionEqInput_holds : GGStepTwoUnitaryFusionEqInput :=
  ggStepTwoUnitaryFusionEqInput_of_bstarFrame ggUnitaryBstarFrameInput_holds

theorem ggStepTwoLinearFusionEqInput_holds : GGStepTwoLinearFusionEqInput :=
  ggStepTwoLinearFusionEqInput_of_bstarFrame ggUnitaryBstarFrameInput_holds

theorem ggStepTwoUnitaryFusionLargeInput_of_centralizer (hI1 : GGUnitaryBstarCentralizerInput) :
    GGStepTwoUnitaryFusionLargeInput :=
  ggStepTwoUnitaryFusionLargeInput_of_bstarFrame ggUnitaryBstarFrameInput_holds hI1

end Inputs

end CFSG.StandardType
