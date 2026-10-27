module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocZSNL
public import CFSG.Quasithin.Recognition.SzR1cHolds

public section

namespace CFSG.Quasithin.SzSurvLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem hZS_of_nonab {G : Type} [Group G] [Finite G]
    {K1 L2 S Zs : Subgroup G} (h : R1SettingLegacyBare K1 L2 S Zs)
    (hBen : ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K1))
    (hKZ : K1 ≤ Subgroup.centralizer (omegaOneCenterOf S : Set G))
    (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥) :
    ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs := by
  have hL : IsL2Quot 2 (OTwoQuot K1) ∨ IsL2Quot 3 (OTwoQuot K1) := by
    by_contra hcon
    push Not at hcon
    exact f112R1c_holds G K1 L2 S Zs h hBen hcon.1 hcon.2
  exact hZS_of_nonab_L h hL hKZ hna

end CFSG.Quasithin.SzSurvLoc
