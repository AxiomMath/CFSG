module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Defs
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

omit [Finite G] in
theorem K1_le_g0Of (T M H K1 : Subgroup G) : K1 ≤ g0Of T M H K1 :=
  (le_sup_left : K1 ≤ K1 ⊔ l2Of T H (yOfL22 T M)).trans le_sup_left

theorem Core3Ctx.embLoc (h37 : A37ForSQTK) (c : Core3Ctx T M H K1 L M₁) :
    H13.EmbLoc G (sOf T K1) (g0Of T M H K1) K1 L := by
  have hB : K1 ∈ lFamily (sOf T K1) := c.st.notation_.cComp_mem
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot c.st.hyp.qtke c.st.hyp.simple
    c.st.hyp.nonabelian c.pCore_ne
  refine ⟨c.st.hyp.simple, c.st.hyp.nonabelian, c.st.hyp.qtke, c.pCore_ne,
    isSylowTwoOf_g0 c.inM c.sylow, K1_le_g0Of T M H K1, hB, inf_le_right,
    ⟨c.mem, c.lt_L.le, fun Y hY hK1Y => ?_⟩, c.lt_L⟩
  exact lemma_1_2_4_unique (h37 _ hQ) hB hY c.mem hK1Y c.lt_L.le

end S1421

end CFSG.Quasithin
