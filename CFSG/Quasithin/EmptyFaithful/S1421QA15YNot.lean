module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Split
public import CFSG.Quasithin.EmptyFaithful.S1421QA15H
public import CFSG.Quasithin.EmptyFaithful.S1421QA15C1
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Blk

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem core3He_false_of_isSylowTwoOf_rOf
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}
    (c : S1421.Core3Ctx T M H K1 L M₁) (hc : CharTwo (S1421.g0Of T M H K1))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hsyl : IsSylowTwoOf (S1421.rOf T M K1 ⊓ L) L) : False := by
  have hR := S1421.isTwoRadicalIn_g0_rOf c
  have hcgs := S1421.cgsIn_g0_rOf_le c
  have hMs := S1421.isSQTKIn_g0 c
  rcases S1421.le_or_isChi0Block_of_asc129_used (h129 G) hc hMs hR hcgs c.mem hq hsyl with
    hle | hblk
  · exact c.st.notation_.not_le (c.lt_L.le.trans hle)
  · have hK1 : K1 ∈ cComp (K1 ⊔ S1421.sOf T K1) := c.st.notation_.cComp_mem
    exact S1421.false_of_isChi0Block_of_perfect_lt c.mem c.normal
      (S1421.isSylowTwoOf_g0 c.inM c.sylow) inf_le_right c.lt_L (perfect_of_mem_cComp hK1)
      (ne_bot_of_mem_cComp hK1) hblk

theorem core3HeYnot_of_h129 (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G) :
    Core3HeYnot := by
  intro G _ _ T M H K1 L M₁ c hc hq hY
  exact core3He_false_of_isSylowTwoOf_rOf h129 c hc hq
    (S1421.isSylowTwoOf_rOf_inf_of_not_le c hY)

theorem core3HeYin_of_syl (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (hs : Core3HeSyl) : Core3HeYin := by
  intro G _ _ T M H K1 L M₁ c hc hq hY
  exact core3He_false_of_isSylowTwoOf_rOf h129 c hc hq (hs G T M H K1 L M₁ c hc hq hY)

end CFSG.Quasithin
