
module

public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.ThSchreier.AutAssembly

@[expose] public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier TauCeti Pointwise MulAction

theorem isCoatom_map_of_bijective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Bijective f) {L : Subgroup G} (hL : IsCoatom L) : IsCoatom (L.map f) := by
  refine ⟨fun ht => hL.1 ?_, fun L' hlt => ?_⟩
  · rw [← Subgroup.comap_map_eq_self_of_injective hf.1 L, ht, Subgroup.comap_top]
  · have hle : L ≤ L'.comap f := fun x hx => hlt.le ⟨x, hx, rfl⟩
    have hne : L ≠ L'.comap f := by
      intro heq
      apply hlt.ne
      rw [heq, Subgroup.map_comap_eq_self_of_surjective hf.2]
    have htop := hL.2 _ (lt_of_le_of_ne hle hne)
    rw [← Subgroup.map_comap_eq_self_of_surjective hf.2 L', htop,
      Subgroup.map_top_of_surjective f hf.2]


end CFSG.Sporadic.Th.Kernel
