module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step32
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepF2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepF3b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss32DEFAt_of (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h28 : Hss28At H M)
    (h113a : Hss113aAt H M) (h113c : Hss113cAt H M) : Hss32DEFAt H M := by
  intro hb3 α β α' hc hv hcomm hn
  rcases Nat.even_or_odd (bMin H M) with heven | hodd
  · have hb4 : 4 ≤ bMin H M := by
      obtain ⟨k, hk⟩ := heven
      omega
    obtain ⟨u, c, c', y, P⟩ := stepF_points hA h27 h28 h113a hc hv hcomm hb4 heven hn
    obtain ⟨V⟩ := stepF_VuModule hA h113c P
    by_cases hR : ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)
    · exact stepF_D1 hA h27 h28 h113a hc hv hcomm hb4 hn P h113c heven hR
    · exact stepF_D2 hA h27 h28 h113a hc hv hcomm hb4 hn P V hR
  · exact hss32_odd_false hA h27 h28 h113a h113c hc hv hcomm hb3 hodd hn

end F53.Stellmacher

end CFSG.Quasithin
