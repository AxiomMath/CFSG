module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsLie

public section

namespace CFSG.Quasithin.H13.Sec53F.Yam

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem lieModelFacts_of_std {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (h : ∀ (Y : Type) [Group Y] (f : ℕ), IsSec53Param t m f → LieModel Y t m 2 f →
      ∃ (C : Type) (_ : Group C) (_ : Finite C) (U P₀ P₁ : Subgroup C),
        YamStd C U P₀ P₁ ∧ LieFactsOf U P₀ P₁ ∧ Nonempty (Y ≃* C)) :
    LieModelFacts t m := by
  intro Y _ f hpar hY
  obtain ⟨C, _, _, U, P₀, P₁, S, F, ⟨e⟩⟩ := h Y f hpar hY
  exact ⟨Finite.of_equiv C e.symm.toEquiv, fun TY M₁ M₂ hpair =>
    lieFactsOf_of_yamStd S F e hpair⟩

end CFSG.Quasithin.H13.Sec53F.Yam
