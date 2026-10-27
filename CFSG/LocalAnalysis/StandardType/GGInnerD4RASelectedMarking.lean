module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAMarking
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RegimeDefs

public section

namespace CFSG.StandardType.GGInnerD4RAParts

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA

theorem raSelectedMarking_of_self (h : S2MathAs51600RAMarking.RAModelSelfMarking) :
    S2MathAs51600RAMarking.RASelectedMarking := by
  intro X _ A σ hσ hmark
  obtain ⟨hX, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .A ∨ lab.tag = .twA := by
    obtain ⟨R, _, I, F, -, -, θ, hRA, -⟩ := largeEvenRawDatum_exists hraw
    rw [CFSG.StandardType.GGKacRA] at hRA
    rcases hRA with ⟨ht, -⟩ | ⟨ht, -⟩
    · exact Or.inl ht
    · exact Or.inr ht
  have hraw' := h lab hlab htag
    (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : X ⧸ Subgroup.center X ≃* R,
        CFSG.StandardType.GGKacRA lab 3 ∧ CFSG.StandardType.GGInducedInn A θ I) hraw
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hRA, hInd⟩, hguard⟩
  exact ⟨hs, hna, θ, ⟨hRA, hInd⟩,
    hguard hs hna (CFSG.StandardType.ggInducedAut θ σ) (hInd σ hσ)⟩

end CFSG.StandardType.GGInnerD4RAParts

end
