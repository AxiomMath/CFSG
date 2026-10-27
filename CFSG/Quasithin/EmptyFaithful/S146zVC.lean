module

public import CFSG.Quasithin.EmptyFaithful.SBc17Out5

public section

namespace CFSG.Quasithin.S146zV

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.SBc17
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_innerSub_of_isAltType_five {J : Subgroup G} (h5 : IsAltType J 5) {k : G}
    (hk : k ∈ Subgroup.normalizer (J : Set G)) (hk5 : k ^ 5 = 1) : k ∈ innerSub J := by
  obtain ⟨α, hα, hker, -⟩ := h5
  exact mem_innerSub_of_out5 hα hker (out5Inner_alternating (by norm_num)) hk hk5

variable [Finite G]

end CFSG.Quasithin.S146zV
