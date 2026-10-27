module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQMid3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem input15124SevenV2InQ_of (hK : KnownFacts15122Types) (h15 : StageLemma1515CE)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Input15124SevenV2InQ := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h7 hb
  exfalso
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hV : V154 T Mc M = VZ T M := hS.hV
  obtain ⟨hVe, d, -⟩ := exists_seven7Data hq hMf h7 hV
  have h15' : Lemma1515Concl T Mc M := h15 G T Mc M hq hMf hc.ctx.ce
  obtain ⟨-, hV₂Y, hnorm, hfpf⟩ := v2_data hK h15' hc hb
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  refine V2InQ.false_of_data d (hS.z1_le.trans inf_le_left) hS.v2_le (hS.decomp_seven h7).1
    (hS.ranks_seven h7).1 (hS.ranks_seven h7).2.2.1 (fun ℓ hℓ a ha => ?_) hb hV₂Y hnorm hfpf
    (fun x hx hodd => V2InQ.normalizes_L_of_odd h37 h38 hc hx hodd)
  have h1 := Subgroup.mem_centralizer_iff.1 (hLG hℓ) a ha
  calc ℓ * a * ℓ⁻¹ = (ℓ * a) * ℓ⁻¹ := rfl
    _ = (a * ℓ) * ℓ⁻¹ := by rw [← h1]
    _ = a := by group

end CFSG.Quasithin
