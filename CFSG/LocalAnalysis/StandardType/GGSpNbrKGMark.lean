module

public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGQuot
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGInj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem largeEvenMarking_mono_labelAll {X : Type*} [Group X] {P Q : LargeEvenMarkProp X}
    {P' : LargeEvenLabel → LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (P' lab))
    (hPQ : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), IsSimpleGroup R → P lab R I F θ → P' lab R I F →
        Q lab R I F θ)
    (h : LargeEvenMarking X P) : LargeEvenMarking X Q := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (hall lab hlab _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hPQ lab R I F θ hs hθ hP'⟩

end CFSG.StandardType
