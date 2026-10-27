module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4LocMain
public import CFSG.Quasithin.Vol2.TwoF4F48Cert

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

set_option linter.unusedSectionVars false


theorem f431_clause2 :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H₁ H₂ : Subgroup G) (z : G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂) (IsTwistedF4Over 1) →
      Nonempty (oTwoQuot ↥H₁ ≃* Sz 0) → z ∈ H₁ → z ≠ 1 → z ^ 2 = 1 →
      H₁ ≤ Subgroup.centralizer ({z} : Set G) → Subgroup.centralizer ({z} : Set G) ≤ H₁ →
      Nonempty (G ≃* MulAut CFSG.Open.quasithinTits) :=
  fun G _ _ _ => f431_clause2_of_inputs H13.F45Ru.f45TwoF4 H13.TwoF4F48.f48TwoF4 twoF4LocalCent G

end CFSG.Quasithin.H13.F431.TwoF4
