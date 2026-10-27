module

public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.HypothesisC

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

attribute [local instance] blockKernel_normal

theorem blockKernel_le_normalizer (hC : HypothesisC D) :
    blockKernel hC.alpha ≤ Subgroup.normalizer hC.alpha := by
  intro g hg
  rw [mem_blockKernel_iff] at hg
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  exact hg hC.alpha (mem_blockClass_self hC.alpha)

end CFSG.OddTranspositions
