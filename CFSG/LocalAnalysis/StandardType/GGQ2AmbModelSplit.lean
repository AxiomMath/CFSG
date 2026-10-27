module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosAmb

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2_marking_with_label {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    (h : LargeEvenMarking X P) :
    ∃ lab : LargeEvenLabel, LargeEvenMarking X (fun lab' _ _ _ _ _ => lab' = lab) := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨lab, hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, _⟩
  exact ⟨hs, hna, θ, rfl⟩

end CFSG.StandardType

end
