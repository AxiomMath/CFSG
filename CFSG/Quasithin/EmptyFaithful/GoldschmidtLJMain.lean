module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtLJComm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtLJCtx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem input15120LJ_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h1416 : StageLemma1416) (h15 : StageLemma1515CE) : Input15120LJ := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar
  have hq := hc.ctx.qtfe
  have hM := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hLM : ¬ L ≤ M :=
    lemma_15_1_20_one (h1416 G T Mc hq).1 hM (h15 G T Mc M hq hM hc.ctx.ce) hc.hL
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hSet.pCore_g1_ne_bot hq hM
  have hS1 : s1516 T Z₁ ≠ ⊥ := fun h =>
    hpc (le_bot_iff.1 (h ▸ pCoreOf_le_of_isSylowTwoOf hc.h18.four))
  have hNJ : Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS hc.h18.four.2.1 hS1).trans hc.h17.cgs
  have hlocal := quasithinIsLocal_iff_lFamily.mp hc.hL.mem.2
  have hLX : L ∈ cComp (L ⊔ s1516 T Z₁) := cComp_of_isLocal hc.hL.mem.2
  exact LJ.commutator_thompsonJ_eq_of_le_normalizer hlocal.2.1 (subnormal_of_mem_cComp hLX)
    (LJ.thompsonJ_le_normalizer_of_ctx15120 h37 h38 hc hchar) (perfect_of_mem_cComp hLX)
    hc.hL.quasi hNJ hLM

end CFSG.Quasithin
