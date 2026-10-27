module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.H13.NQBlockComplementaryLayer

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem sqtkCLayerPerfectResidual_proved
    : SQTKCLayerPerfectResidual :=
  fun G _ _ hG hO2 => (Vol2Native.a39ForSQTKCat_proved G ⟨inferInstance, hG.1, hG.2, hO2⟩).1

theorem sylowNormalizedLocalNormalComponent_proved
    : SylowNormalizedLocalNormalComponent := by
  intro G _ _ _ hnab hK H S B hH hS hBH hB hSB
  obtain ⟨⟨L, hL, hBL, hLn, huniq⟩, hmax⟩ :=
    Vol2Native.normal_containing_cComp_of_le_normalizer hnab hK hH hS hBH hB hSB
  refine ⟨L, ⟨hL, hBL⟩, fun L' hL' => huniq L' hL'.1 hL'.2, hLn, fun hm => ?_⟩
  obtain ⟨hBc, hBn⟩ := hmax hm
  exact ⟨(huniq B hBc le_rfl).symm, hBn⟩

theorem originalKEscapingSourceY_of_sourceY
    (hF : OriginalKContainingConfinement) (hA : AllComponentsContainedSourceY)
    (hB : ComplementaryEscapeSimpleSourceY) : OriginalKEscapingSourceY :=
  originalKEscapingSourceY_of_cLayer sqtkCLayerPerfectResidual_proved hF hA hB

end CFSG.Quasithin.H13.NQBlock
