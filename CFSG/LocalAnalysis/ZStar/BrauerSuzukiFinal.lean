module

public import CFSG.LocalAnalysis.ZStar.ComponentFourierSpectral
public import CFSG.LocalAnalysis.ZStar.TerminalAssembly
public import CFSG.LocalAnalysis.ZStar.BrauerSuzukiShortcut

public section

namespace CFSG

namespace ZStar.BrauerSuzukiFinal

open ZStar.BrauerSuzukiShortcut
open ZStar.CentralizerInduction
open ZStar.TerminalAssembly
open ZStar
open ZStar.TransferReduction

theorem glauberman_zStar (G : Type) [Group G] [Fintype G]
    (t : G) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  have ht : Isolated t := hisolated
  apply zStar_of_stable_components_and_unique_involution
    (ht := ht) (ht2 := ht2)
  · intro X _ _ D i hi
    have h :=
      ZStar.ComponentFourierSpectral.selected_componentCharacter_centralizerOddCoreStable
        D i hi
    simpa only [
      ZStar.AbstractStepV.CentralizerOddCoreStable,
      ZStar.WedderburnCharacters.componentCharacter,
      ZStar.TwoAdicWedderburn.componentCharacter_eq_matrixTrace] using h
  · intro X _ _ x _hx hx2 _hmin P hxP hunique hperfect
    by_cases hx1 : x = 1
    · subst x
      exact zStarConclusion_one
    · exact zStarConclusion_of_perfect_uniqueInvolution_brauerSuzuki
        hx1 hx2 P hxP hunique hperfect

end ZStar.BrauerSuzukiFinal

end CFSG
