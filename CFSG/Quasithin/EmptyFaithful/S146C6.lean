module

public import CFSG.Quasithin.EmptyFaithful.S146C5
public import CFSG.Quasithin.EmptyFaithful.S146R7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem stage146FRank_of (h5 : Stage1461Five) : Stage146FRank := by
  intro G _ _ T M S hB K U₁ U₂ s u hd
  refine ⟨?_, S.four_le_mIdx_of_bdata h5 hB hd⟩
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨-, hL3, hKeq, -⟩ := hd.c24
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  exact four_lt_relIndex_of_kbarIsL3Two
    (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hG.1.1) (le_of_mem_cComp hd.hK) hKn hL3

theorem stageSection146_of_inputs_eight (h1413 : StageLemma1413) (h11 : StageLemma14111)
    (h113 : StageLemma14113) (hedge : GoldschmidtEdgeBoundSubgroups.{0})
    (h2 : Stage1461Two) (h3 : Stage1461Three) (h5 : Stage1461Five)
    (h12 : Stage14612Part) (h15 : Stage14615) (h17 : Stage14617)
    (h20 : Stage14620) (h21 : Stage14621) (h22 : Stage14622)
    (h23 : Stage14623) (hD4 : Stage146D4) (h24 : Stage14624)
    (hF2 : Stage146FH2) (hF3 : Stage146FFour)
    (h9 : Stage1469) (h105 : Stage14610Five) (h634 : Stage1463Four) : StageSection146 :=
  stageSection146_of_inputs_seven h1413 h11 h113 hedge h2 h3 h5 h12 h15 h17 h20 h21 h22 h23 hD4
    h24 (stage146FRank_of h5) hF2 hF3 h9 h105 h634

end CFSG.Quasithin
