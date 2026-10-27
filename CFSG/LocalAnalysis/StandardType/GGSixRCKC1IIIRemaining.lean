module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGlue
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1III

public section


namespace CFSG.StandardType.RCKRP

open CFSG.Open (StatedLieTag)

theorem rckRowIII_tag_eq_E7_or_E8 {X : Type} [Group X] {t : StatedLieTag} {n : ℕ}
    {ψ : (ggU t n 1).K →* X} {G₀ K B₁ : Subgroup X}
    (hpres : GGPresentsG0 G₀ (ggU t n 1).D t n 1 ψ)
    (hcls : RCKClassicalTag t → ∃ s : StatedLieTag, RCKClassicalTag s ∧ s ≠ .PSU ∧
      s ≠ .PSL ∧ s ≠ .PSp ∧ s ≠ .POmegaMinus ∧ RCKClassicalModelIDAt s K B₁)
    (hE6 : t ≠ .E6) (hF4 : t ≠ .F4) (htw : t ≠ .twistedE6)
    (hplus : ¬ RCKClassicalModelIDAt .POmegaPlus K B₁) :
    t = .E7 ∨ t = .E8 := by
  unfold GGPresentsG0 at hpres
  rcases rckRPG_tag_trichotomy t n 1 hpres.1.1 hpres.1.2 with hc | hx
  · obtain ⟨s, hs, hPSU, hPSL, hPSp, hMinus, hmodel⟩ := hcls hc
    unfold RCKClassicalTag at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hPSL
    · exact absurd rfl hPSU
    · exact absurd rfl hPSp
    · exact absurd hmodel hplus
    · exact absurd rfl hMinus
  · unfold GGExcFive at hx
    rcases hx with h | h | h | h | h
    · exact absurd h hF4
    · exact absurd h hE6
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h htw

end CFSG.StandardType.RCKRP

namespace CFSG.StandardType.RCKC1

theorem rckRowK2IIIAtTwoRemaining_holds : RCKRowK2IIIAtTwoRemaining := by
  intro X _ _ t n ψ p G₀ A B₁ D J L
    _ hG0 _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ K _ _ _ _ _ _ _ _ _ _ _ hModel _ htE6 htF4 htTw htE7 htE8 hNativePlus
  exact ((RCKRP.rckRowIII_tag_eq_E7_or_E8 hG0 hModel htE6 htF4 htTw hNativePlus).elim htE7
    htE8).elim

end CFSG.StandardType.RCKC1
