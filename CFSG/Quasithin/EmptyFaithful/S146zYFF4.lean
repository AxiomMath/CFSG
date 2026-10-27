module

public import CFSG.Quasithin.EmptyFaithful.S146zYFF3
public import CFSG.Quasithin.EmptyFaithful.S146zYCfg

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Assembly.LowTwoRank CFSG.Blueprint


theorem facts134Five_f4Even :
    ∀ n : ℕ, NoE25Config fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n := by
  intro n A _ _ L P T hL hcfg
  have hS := E25Config.isSylowTwoOf_inf hcfg
  refine TwoF4.false_of_twistedF4_five hL (P := P.subgroupOf L) (U := (T ⊓ L).subgroupOf L) ?_ ?_
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hS) ?_
  · rw [← hcfg.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv
  · intro x hx
    exact Subtype.ext (by simpa using hcfg.exp x (Subgroup.mem_subgroupOf.mp hx))
  · intro u hu x hx
    obtain ⟨y, hy, s, hs, he⟩ := E25Config.mul_inf hcfg u (Subgroup.mem_subgroupOf.mp hu) x
      (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨⟨y, hcfg.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, ⟨s, hs.2⟩,
      Subgroup.mem_subgroupOf.mpr hs, Subtype.ext he⟩

end CFSG.Quasithin.S146zY
