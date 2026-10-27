module

public import CFSG.LocalAnalysis.StandardType.GGE6KGLayerInputTw
public import CFSG.LocalAnalysis.StandardType.GGKGLayersHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem largeEvenLabelAll_kgLayers_E6 {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGE6KGLayers R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h3
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  intro _ _
  exact KGL.kgLayers_E6_holds K n hΛ.1 hK h3

theorem ggE6KGLayerInput_of_tw (h : GGE6KGLayerInputTw) : GGE6KGLayerInput :=
  fun lab hdep hΛ => hdep.elim
    (fun ⟨htag, h3⟩ => largeEvenLabelAll_kgLayers_E6 hΛ htag h3)
    (fun ⟨htag, h3⟩ => h lab htag h3 hΛ)

end CFSG.StandardType

end
