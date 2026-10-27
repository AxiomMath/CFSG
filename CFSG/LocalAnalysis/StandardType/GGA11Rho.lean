module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs
public import CFSG.LocalAnalysis.StandardType.GGA11RhoMk
public import CFSG.LocalAnalysis.StandardType.GGA11RhoS9
public import CFSG.LocalAnalysis.StandardType.GGA11RhoInj
public import CFSG.LocalAnalysis.StandardType.GGA11RhoClos

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

theorem a11RhoInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (Φ : Fin 4 → SL 9 →* G),
      (∀ l, Function.Injective (Φ l)) → Coherent Φ → ∃ ρ : Equiv.Perm (Fin 12) →* G, A11RhoSpec Φ ρ := by
  intro G _ _ Φ hinj hcoh
  obtain ⟨ρ, hρ⟩ := a11RhoMkInput_holds G Φ hcoh
  obtain ⟨h9, hst⟩ := a11RhoS9Input_holds G Φ ρ hcoh hρ
  obtain ⟨hcl, hrg⟩ := a11RhoClosInput_holds G Φ ρ hcoh hρ
  exact ⟨ρ, ⟨a11RhoInjInput_holds G Φ ρ (hinj 3) hρ, h9, hst⟩, hcl, hrg⟩

end CFSG.StandardType.A11

end
