module

public import CFSG.Quasithin.EmptyFaithful.S14612DC
public import CFSG.Quasithin.EmptyFaithful.S146F13

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Input14614SolDec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3 →
      (∃ H₀ H₁ H₂ : Subgroup G, ∃ t : G, IsDecP T M H p H₀ H₁ H₂ t) →
      conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H → Group.IsSolvable ↥(mcOf T)

theorem input14614Sol_of_dec (h12 : Stage14612PartP) (i : Input14614SolDec) : Input14614Sol := by
  intro G _ _ T M S H PQ p hred hmax hp3 hK
  exact i G T M S H PQ p hred hmax hp3 (h12 G T M S H PQ p hred hmax).2 hK

end CFSG.Quasithin
