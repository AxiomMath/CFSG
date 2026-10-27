module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Core
public import CFSG.Quasithin.EmptyFaithful.A38c17Core

public section

namespace CFSG.Quasithin.A312U3

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem su3OddIrr_A38c17_of (h : SU3OddIrr) : CFSG.Quasithin.A38c17.SU3OddIrr := by
  intro p hpf hp2 K _ _ hK M hodd hirr
  have hp : p.Prime := hpf.out
  have h1 := h p hp2 K hK
  rw [pow_one] at h1
  have hirr' : IsIrrIn (StatedSU 3 p K) M := by
    intro W hW
    apply hirr W
    intro g hg w hw
    exact hW ⟨(g : GL (Fin 3) K), g, hg, rfl⟩ w hw
  rcases h1 M hodd hirr' with htop | hsolv | ⟨hp5, hHat, hz⟩
  · exact Or.inl htop
  · exact Or.inr (Or.inl hsolv)
  · refine Or.inr (Or.inr ⟨hp5, hHat, ?_⟩)
    have hcardSc : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 p K)) = 3 := by
      have := (CFSG.Quasithin.A38c17.scalars_card hp (by rw [pow_one]; exact hK)).2 hp5
      rwa [pow_one] at this
    set Z' : Subgroup ↥(StatedSU 3 p K) :=
      (Subgroup.center ↥(perfectCore M)).map (perfectCore M).subtype with hZ'
    have hle : Z' ≤ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 p K) := by
      rintro _ ⟨w, hw, rfl⟩
      exact hz w hw
    have hcardZ' : Nat.card Z' = 3 := by
      rw [hZ', Subgroup.card_map_of_injective (perfectCore M).subtype_injective]
      exact hHat.2.1
    have heq : Z' = (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 p K) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardSc, hcardZ'])
    rw [← heq]
    exact Subgroup.map_subtype_le _

end CFSG.Quasithin.A312U3
