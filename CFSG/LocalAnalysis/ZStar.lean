module

public import CFSG.LocalAnalysis.ZStar.StepVI
public import CFSG.LocalAnalysis.ZStar.TwoAdicStepVII
public import CFSG.LocalAnalysis.ZStar.TwoAdicCharacterTerminal
public import CFSG.LocalAnalysis.ZStar.TerminalAssembly
public import CFSG.LocalAnalysis.ZStar.BrauerSuzukiFinal

public section

namespace CFSG

namespace ZStar

theorem glauberman_zStar (G : Type) [Group G] [Fintype G]
    (t : G) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  exact ZStar.BrauerSuzukiFinal.glauberman_zStar G t ht1 ht2 hisolated

end ZStar

end CFSG
