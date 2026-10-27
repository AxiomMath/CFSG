module

public import CFSG.OddTranspositions.SixSixKernel
public import CFSG.OddTranspositions.SixSix
public import CFSG.OddTranspositions.SixSixSimple

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem blockKernel_eq_bot_of_simple_minimalNormal (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {M : Subgroup G} (hM : Asc72.IsMinimalNormal M) (hMs : IsSimpleGroup M)
    (hMc : Subgroup.centralizer (M : Set G) = ⊥) : blockKernel hC.alpha = ⊥ := by
  classical
  by_contra hK
  haveI : M.Normal := hM.1
  have hMK : M ≤ blockKernel hC.alpha := le_blockKernel_of_ne_bot hC hrad hK hM
  have hMα : M ≤ Subgroup.normalizer hC.alpha := hMK.trans (blockKernel_le_normalizer hC)
  have hMcl := le_closure_alpha_of_le_normalizer hC hMs hMc hMα
  obtain ⟨b, hbD, hb⟩ := exists_mem_D_centralizes_alpha hC
  have hcl : Subgroup.closure hC.alpha ≤ Subgroup.centralizer {b} := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hb a ha).eq
  have hbM : b ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have := hcl (hMcl hm)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  rw [hMc, Subgroup.mem_bot] at hbM
  exact hC.setup.oddT.ne_one hbD hbM

end CFSG.OddTranspositions
