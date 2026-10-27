module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.EmptyFaithful.S1421QA27Surv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SzSurvLoc

variable {G : Type} [Group G]

theorem card_sup_dvd {K1 L2 S : Subgroup G} {Y : Type} [Group Y]
    (ψ : ↥(K1 ⊔ bigB K1 L2 S) →* Y) (hψ : Function.Injective ψ) :
    Nat.card ↥(K1 ⊔ S) ∣ Nat.card Y := by
  have hX : K1 ⊔ S ≤ K1 ⊔ bigB K1 L2 S := S1421QA27.sup_le_sup_bigB
  exact Subgroup.card_dvd_of_injective (ψ.comp (Subgroup.inclusion hX))
    (hψ.comp (Subgroup.inclusion_injective _))

end SzSurvLoc

end CFSG.Quasithin
