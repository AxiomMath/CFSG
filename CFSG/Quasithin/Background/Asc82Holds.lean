module

public import CFSG.Quasithin.Background.C24PfD
public import CFSG.Quasithin.Background.B15P4Layer2Final

public section

namespace CFSG.Quasithin

namespace Asc82Pf

theorem isComponentOf_of_isComponent_subgroupOf {G : Type*} [Group G] {X K : Subgroup G}
    (hKX : K ≤ X) (hc : CFSG.IsComponent (K.subgroupOf X)) : CFSG.Open.IsComponentOf K X := by
  have hq : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX) hc.1
  have hsub := A3.subnormal_map X.subtype ((CFSG.isComponent_iff_open _).mp hc).2.1
  rw [Subgroup.map_subgroupOf_eq_of_le hKX, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hsub
  exact ⟨hKX, hsub, Group.isPerfect_def.mp hq.1, hq.2.1⟩

end Asc82Pf

theorem asc82Thm2_holds : Asc82Thm2 :=
  fun W _ _ hW X A K _ hA hKX hK =>
    B15P4.asB15Part4 W hW X A hA K (Asc82Pf.isComponentOf_of_isComponent_subgroupOf hKX hK)

end CFSG.Quasithin
