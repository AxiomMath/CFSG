module

public import CFSG.Quasithin.EmptyFaithful.S151S5B
public import CFSG.Quasithin.EmptyFaithful.S151S4F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem charTwo_sup_s1516_of_listA {G : Type} [Group G] [Finite G]
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hchar : CharTwo L)
    (hA : ListA15120 L) : CharTwo (L ⊔ s1516 T Z₁) := by
  obtain ⟨n, hn, hLn⟩ := hA
  have hLloc : L ∈ cComp (L ⊔ s1516 T Z₁) := cComp_of_isLocal hc.hL.mem.2
  have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := S151S4.center_eq_bot_of_isPSL2 hLn
  refine S151S5.charTwo_sup_of_simple_comp hc.h18.four.2.1 (subnormal_of_mem_cComp hLloc)
    (perfect_of_mem_cComp hLloc) hchar hc.hL.quasi ?_
  intro x hx
  have hxc : x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.mem_center_iff.mpr hx
  rw [hcenter] at hxc
  exact Subgroup.mem_bot.mp hxc

theorem input15120WreathChar_holds : Input15120WreathChar := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hA _ _
  exact charTwo_sup_s1516_of_listA hc hchar hA

end CFSG.Quasithin
