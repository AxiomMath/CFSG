module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
import CFSG.LocalAnalysis.WeakClosure81.A6Case.Center
import CFSG.LocalAnalysis.WeakClosure81.A6Case.Lift
import CFSG.LocalAnalysis.WeakClosure81.A6Case.Centralize

public section

namespace CFSG.LocalAnalysis.WeakClosure81.A6Case

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}


theorem not_isBarMap_alt6 (h : Hyp711 V H E)
    {ψ : ↥(kSub V H E) →* alternatingGroup (Fin 6)}
    (hψ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) ψ) : False := by
  obtain ⟨U, hU, d, hd, ρ, hρK, c, hcK, hρ, hρ1, hc, hρc, hdρ, hdc, hcρ⟩ :=
    exists_inverted_pair_of_isBarMap h hψ
  exact false_of_inverted_pair h hU hd hρK hcK hρ hc hρc hdρ hdc hcρ hρ1

theorem sevenElevenASixInput_holds (G : Type) [Group G] [Finite G] : SevenElevenASixInput G := by
  intro V H E h X _ φ hφ hA6 _hVbar
  obtain ⟨e⟩ := hA6
  rcases card_center_eq_one_or_three h hφ e with h1 | h3
  · obtain ⟨ψ, hψ⟩ := exists_isBarMap_alt6 hφ e h1
    exact (not_isBarMap_alt6 h hψ).elim
  · exact h3

end CFSG.LocalAnalysis.WeakClosure81.A6Case

end
