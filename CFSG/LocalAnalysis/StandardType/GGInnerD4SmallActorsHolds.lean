module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallContracts
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestExcl

public section

namespace CFSG.StandardType.GGInnerD4SmallParts

open CFSG CFSG.Assembly CFSG.StandardType

private theorem ltrsm5_ggInnSubsetLabel_small {lab : LargeEvenLabel}
    (h : S2MathAs51600Small.TableRegime lab ∨ lab.tag = .twB2) :
    GGInnSubsetLabel lab := by
  rcases h with (h | h | h) | h
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem smallInnerActorsInput_holds :
    S2MathAs51600Small.SmallInnerActorsInput := by
  intro lab hlab h
  have hG := ltrsm5_ggInnSubsetLabel_small h
  have H := largeEvenLabelAll_subset_inn_ext (lab := lab) hlab hG
  intro Q hQ
  refine largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.1, ?_⟩) (H Q hQ)
  intro hs hna τ hτ
  obtain ⟨r, hr⟩ := hq.2 hs hna hτ
  exact ⟨r, hr.symm⟩

end CFSG.StandardType.GGInnerD4SmallParts

end
