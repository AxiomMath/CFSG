module

public import CFSG.Quasithin.H13.NQCoreEscapingCore
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem isCComponent_of_isSimpleGroup {S : Subgroup H} [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) (hsub : S.IsSubnormal) : CFSG.IsCComponent S := by
  refine ⟨?_, commutator_eq_self_of_isSimpleGroup hS, hsub, fun K hKS hK1 _ hKsub => ?_⟩
  · intro hb
    have : Nontrivial ↥S := IsSimpleGroup.toNontrivial
    exact (nontrivial_iff_ne_bot S).mp this hb
  · rcases (hKsub.subgroupOf (K := S)).eq_bot_or_top_of_isSimpleGroup inferInstance with h | h
    · apply hK1
      have h1 := congrArg (Subgroup.map S.subtype) h
      rwa [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot, inf_of_le_left hKS.le] at h1
    · exact hKS.not_ge (Subgroup.subgroupOf_eq_top.mp h)

end CFSG.Quasithin.H13.NQCore
