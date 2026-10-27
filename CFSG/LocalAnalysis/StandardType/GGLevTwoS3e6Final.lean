module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e6Tc2
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e6Link

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem levTwoS3e6_excFinite :
    ExcFinite Tag.E6 kacE6 := by
  intro D l hD hirr hrank
  obtain ⟨hm, rfl, hpart⟩ := levTwoS3e6_mask_cases D l hD hirr hrank
  rw [hpart]
  have hm' : levTwoS3e6_maskOf D = 29 ∨ levTwoS3e6_maskOf D = 30 ∨ levTwoS3e6_maskOf D = 31 ∨
      levTwoS3e6_maskOf D = 53 ∨ levTwoS3e6_maskOf D = 58 ∨ levTwoS3e6_maskOf D = 60 ∨
      levTwoS3e6_maskOf D = 61 ∨ levTwoS3e6_maskOf D = 62 ∨ levTwoS3e6_maskOf D = 63 ∨
      levTwoS3e6_maskOf D = 116 ∨ levTwoS3e6_maskOf D = 117 ∨ levTwoS3e6_maskOf D = 120 ∨
      levTwoS3e6_maskOf D = 122 ∨ levTwoS3e6_maskOf D = 124 ∨ levTwoS3e6_maskOf D = 125 ∨
      levTwoS3e6_maskOf D = 126 := by
    simpa [levTwoS3e6_survivors] using hm
  rcases hm' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
  · exact levTwoS3e6_tcRoot_29
  · exact levTwoS3e6_tcRoot_30
  · exact levTwoS3e6_tcRoot_31
  · exact levTwoS3e6_tcRoot_53
  · exact levTwoS3e6_tcRoot_58
  · exact levTwoS3e6_tcRoot_60
  · exact levTwoS3e6_tcRoot_61
  · exact levTwoS3e6_tcRoot_62
  · exact levTwoS3e6_tcRoot_63
  · exact levTwoS3e6_tcRoot_116
  · exact levTwoS3e6_tcRoot_117
  · exact levTwoS3e6_tcRoot_120
  · exact levTwoS3e6_tcRoot_122
  · exact levTwoS3e6_tcRoot_124
  · exact levTwoS3e6_tcRoot_125
  · exact levTwoS3e6_tcRoot_126

end CFSG.StandardType.LevTwo
