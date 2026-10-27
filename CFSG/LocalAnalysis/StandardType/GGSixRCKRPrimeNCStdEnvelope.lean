module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.StandardType.LieKnownR2.ExcPos (compRank_ncard_ade)


theorem rckStdEnvelope_holds : RCKStdEnvelope := by
  intro τ hτ S p _ _ a _ _ _ i _
  have hne : (componentRoots (rootCharHom a) i).Nonempty := by
    obtain ⟨⟨α, hα⟩, h⟩ := Quotient.exists_rep i
    exact ⟨α, hα, h⟩
  unfold RCKADEShape
  rcases compRank_ncard_ade hτ (isRootComponent_componentRoots i) hne with h1 | hade
  · exact Or.inl h1
  refine Or.inr ?_
  rcases hk : twistKind S.ρ (rootCharHom a) i with _ | _ | _ | _
  · rcases hade with hA | hD | hE
    · exact Or.inl ⟨rfl, hA⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hD⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hE⟩))))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

end CFSG.StandardType.RCKRP
