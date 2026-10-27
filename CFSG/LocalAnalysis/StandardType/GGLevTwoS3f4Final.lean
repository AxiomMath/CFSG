module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3f4Tc2
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3f4Link

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem

theorem levTwoS3f4_excFinite :
    ExcFinite Tag.F4 kacF4 := by
  intro D l hD hirr hrank
  obtain ⟨s, hs, hli, hrk⟩ := hrank
  have hli' : LinearIndependent ℚ (fun v : s => toRat (v : Fin (Tag.rank Tag.F4) → ℤ)) := by
    have hfun : (fun v : s => toRat (v : Fin (Tag.rank Tag.F4) → ℤ)) =
        (fun v : s => fun i => ((v : Fin (Tag.rank Tag.F4) → ℤ) i : ℚ)) := by
      funext v i
      rw [toRat_apply]
    rw [hfun]
    exact hli
  obtain ⟨hm, hpart⟩ := levTwoS3f4_mask_cases D l hD hirr ⟨s, hs, hli', hrk⟩
  rw [hpart]
  have hm' : (levTwoS3f4_maskOf D = 7 ∧ l.toNat = 4) ∨ (levTwoS3f4_maskOf D = 14 ∧ l.toNat = 4) ∨
      (levTwoS3f4_maskOf D = 15 ∧ l.toNat = 4) ∨ (levTwoS3f4_maskOf D = 23 ∧ l.toNat = 4) ∨
      (levTwoS3f4_maskOf D = 28 ∧ l.toNat = 2) ∨ (levTwoS3f4_maskOf D = 29 ∧ l.toNat = 2) ∨
      (levTwoS3f4_maskOf D = 30 ∧ l.toNat = 2) ∨ (levTwoS3f4_maskOf D = 30 ∧ l.toNat = 4) := by
    simpa [levTwoS3f4_survivors] using hm
  rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact levTwoS3f4_tcRoot_7_4
  · exact levTwoS3f4_tcRoot_14_4
  · exact levTwoS3f4_tcRoot_15_4
  · exact levTwoS3f4_tcRoot_23_4
  · exact levTwoS3f4_tcRoot_28_2
  · exact levTwoS3f4_tcRoot_29_2
  · exact levTwoS3f4_tcRoot_30_2
  · exact levTwoS3f4_tcRoot_30_4

end CFSG.StandardType.LevTwo
