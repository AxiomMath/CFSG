module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8Tc2
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8Filter

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem

theorem levTwoS3b_e8_excFinite :
    ExcFinite Tag.E8 kacE8 := by
  intro D l hD hirr hrank
  obtain ⟨s, hs, hli, hrk⟩ := hrank
  have hli' : LinearIndependent ℚ (fun v : s => toRat (v : Fin (Tag.rank Tag.E8) → ℤ)) := by
    have hfun : (fun v : s => toRat (v : Fin (Tag.rank Tag.E8) → ℤ)) =
        (fun v : s => fun i => ((v : Fin (Tag.rank Tag.E8) → ℤ) i : ℚ)) := by
      funext v i
      rw [toRat_apply]
    rw [hfun]
    exact hli
  obtain ⟨hm, rfl, hpart⟩ := levTwoS3b_e8_mask_cases D l hD hirr ⟨s, hs, hli', hrk⟩
  rw [hpart]
  have hm' : levTwoS3b_e8_maskOf D = 254 ∨ levTwoS3b_e8_maskOf D = 501 ∨ levTwoS3b_e8_maskOf D = 505 ∨
      levTwoS3b_e8_maskOf D = 506 ∨ levTwoS3b_e8_maskOf D = 507 ∨ levTwoS3b_e8_maskOf D = 508 ∨
      levTwoS3b_e8_maskOf D = 509 ∨ levTwoS3b_e8_maskOf D = 510 := by
    simpa [levTwoS3b_e8_survivors] using hm
  rcases hm' with h | h | h | h | h | h | h | h <;> rw [h]
  · exact levTwoS3b_e8_tcRoot_254
  · exact levTwoS3b_e8_tcRoot_501
  · exact levTwoS3b_e8_tcRoot_505
  · exact levTwoS3b_e8_tcRoot_506
  · exact levTwoS3b_e8_tcRoot_507
  · exact levTwoS3b_e8_tcRoot_508
  · exact levTwoS3b_e8_tcRoot_509
  · exact levTwoS3b_e8_tcRoot_510

end CFSG.StandardType.LevTwo
