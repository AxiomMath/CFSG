module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaFork
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggTorusFork_of_excPlusModel
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGExcPlusWeylModelSCr τ p r R I) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusFork p A := by
  intro L' _ _ ψ A hA
  have hsc : GGTorusSelfCent p A := hA.2.2.2.2.2.2.2
  exact ggNEE_torusFork_of_weylModel hτ hp hp2 hsc (h L' ψ A hA)

theorem ggRowFork_EE7
    : GGRowFork ggRowP_EE7 := by
  intro p hp hp2 lab _ hS
  obtain ⟨htag, hpn⟩ := hS
  refine (largeEvenLabelAll_and
    (largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inl htag, hpn⟩)
    (ggNEE_largeEvenLabelAll_model_excPlus hp hp2 (Or.inl htag) hpn)).mono
      fun _ _ _ _ h =>
        ⟨_, h.1, ggTorusFork_of_excPlusModel (Or.inl (by simp [ggNEE_tagOf, htag])) hp hp2 h.2⟩

theorem ggRowFork_EE8
    : GGRowFork ggRowP_EE8 := by
  intro p hp hp2 lab _ hS
  obtain ⟨htag, hpn⟩ := hS
  refine (largeEvenLabelAll_and
    (largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inr (Or.inl htag), hpn⟩)
    (ggNEE_largeEvenLabelAll_model_excPlus hp hp2 (Or.inr htag) hpn)).mono
      fun _ _ _ _ h =>
        ⟨_, h.1, ggTorusFork_of_excPlusModel (Or.inr (by simp [ggNEE_tagOf, htag])) hp hp2 h.2⟩

end CFSG.StandardType

end
