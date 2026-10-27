module

public import CFSG.Sporadic.SmallOddCore.FourGroupBlock
public import CFSG.Sporadic.SmallOddCore.Co3Local

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem commuting_block_co3_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.Co3) := by
  rintro ⟨e⟩
  exact not_escaping_of_local_centralizer_two hq heven hV hJ hΔ hL hML hLH fun u hu B hB =>
    cti_co3_involution_local_component_centralizer_order_two ⟨e⟩ hu hB

end CFSG.Sporadic.SmallOddCore
