module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G]

@[expose] def Hss32DEFAt (H M : Subgroup G) : Prop :=
  3 ≤ bMin H M → ∀ α β α' : Geo H M, IsCritData α β α' → vtype α = true →
    ⁅Zv α, Zv α'⁆ ≠ ⊥ → ¬ Zv β ≤ centerOf (stab β) → False

theorem hss32At_of_defAt {H M S : Subgroup G} (hA : F53Amalgam H M S) (h27 : Hss27S3At H M)
    (h113a : Hss113aAt H M) (hM6 : NoA5Transvection) (hdef : Hss32DEFAt H M) :
    Hss32At H M := by
  intro α β hαβ hv hα
  by_contra hn
  obtain ⟨α', hc⟩ := exists_critData hA hα hαβ
  have hcomm := comm_ne_bot_of_not_central hA hc hn
  have h1 := one_lt_bMin_of_comm_ne hA h113a hM6 hc hv hcomm
  have h2 := bMin_ne_two_of_not_central hA h27 h113a hM6 hc hv hcomm hn
  exact hdef (by omega) α β α' hc hv hcomm hn

end F53.Stellmacher

end CFSG.Quasithin
