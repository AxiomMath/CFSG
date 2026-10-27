module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE7Components
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOmegaMinusTwo
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOmegaPlusTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
import CFSG.LocalAnalysis.StandardType.GGSixUnitaryTwoInnerDiag
import CFSG.LocalAnalysis.StandardType.GGK0MarkedArithmetic
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet
import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVQuot

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType


theorem e7_two_compConfig_modelID
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E7 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (hcfg : RCKRP.RCKCompConfig .E7 n 1 ψ p G₀ A B₁ D J L K e) :
    RCKRP.RCKClassicalModelIDAt .PSU K B₁ ∨
      RCKRP.RCKClassicalModelIDAt .POmegaMinus K B₁ ∨
      RCKRP.RCKClassicalModelIDAt .POmegaPlus K B₁ ∨
      GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K) := by
  have hp3 := prime_eq_three_of_e7_two_compConfig hcfg
  have hcover := e7_two_compConfig_exists_native_cover hcfg
  subst p
  obtain ⟨-, -, hp, -, hA, hBA, hDB, hDcard, hAN, -, hBNJ, -, -, -, -, -, -, -,
    hJcomp, -, -, -, -, -, -, heD, hene, hKcomp, hJK, hOddK⟩ := hcfg
  have hBNK := (RCKRP.le_normalizer_and_exists_isComponentOf_of_plane
    hp hA hBA hDB hDcard hAN hBNJ hJcomp heD hene hKcomp hJK).1
  have hperf : commutator ↥K = ⊤ := hKcomp.2.2.1
  have hna := (ggQuasisimple_centerQuot hKcomp.2.2).2
  have hB3 : ∀ b ∈ B₁, b ^ 3 = 1 := fun b hb => hA.2 b (hBA hb)
  rcases hcover with ⟨hlabel, φ, hφr, hφk⟩ | ⟨hlabel, -⟩ | ⟨hlabel, -⟩ |
    ⟨hlabel, φ, hφr, hφk⟩ | ⟨hlabel, -⟩
  · refine Or.inr (Or.inr (Or.inl ⟨6, 1, φ, le_rfl, hφr, hφk, fun b hb => ?_⟩))
    rw [← hφr] at hperf hlabel
    exact ggPsiInnerDiag_of_cube_of_label_omegaPlus_two (by norm_num) (ggU .POmegaPlus 6 1).D φ
      hperf hlabel (hφr ▸ hBNK hb) (hB3 b hb)
  · have hLie : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 6 2 1 := by
      simpa [markTag, markRank, markDeg] using lieModel_of_markedModel (by decide)
        (GGK0MarkedArithmetic.markedModel_of_label (by simp [LargeEvenInLambda2]) hna hlabel)
    obtain ⟨φ, hφr, hφk, hφd⟩ :=
      exists_unitary_two_innerDiag_presentation hBNK hB3 hperf hOddK (by norm_num) hLie
    exact Or.inl ⟨6, 1, φ, le_rfl, hφr, hφk, hφd⟩
  · have hLie : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 7 2 1 := by
      simpa [markTag, markRank, markDeg] using lieModel_of_markedModel (by decide)
        (GGK0MarkedArithmetic.markedModel_of_label (by simp [LargeEvenInLambda2]) hna hlabel)
    obtain ⟨φ, hφr, hφk, hφd⟩ :=
      exists_unitary_two_innerDiag_presentation hBNK hB3 hperf hOddK (by norm_num) hLie
    exact Or.inl ⟨7, 1, φ, le_rfl, hφr, hφk, hφd⟩
  · refine Or.inr (Or.inl ⟨5, 1, φ, le_rfl, hφr, hφk, fun b hb => ?_⟩)
    rw [← hφr] at hperf hlabel
    exact ggPsiInnerDiag_of_cube_of_label_omegaMinus_two (by norm_num) (ggU .POmegaMinus 5 1).D φ
      hperf hlabel (hφr ▸ hBNK hb) (hB3 b hb)
  · exact Or.inr (Or.inr (Or.inr hlabel))

end CFSG.StandardType.RCKC1
