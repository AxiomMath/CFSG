module

public import CFSG.RankThree.GF2n.Stroth80.Sec311bNatData
public import CFSG.RankThree.GF2n.Stroth80.Sec311bCommAbstract

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement Matrix


theorem stroth311bComm_of_34 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h311a : Stroth311aStatement) : Stroth311bCommStatement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ hR hnotSL T hT
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  obtain ⟨K, fK, finK, hcp, hK, ι, fι, dι, nι, X, φ, hX, hφ, hker, hn', ψ, hψ, r, hr, hgenR⟩ :=
    hc.exists_nat_data h34 h310 hs hR hnotSL
  have hN := h311a G M Q Z B hc n hw hn hno hgen t ht htQ hR
  have hrM : r ∈ M := hc.Rt_le_M t hr
  exact sec311bComm_abstract (Q := Q) (R := Rt M (LB M Q B) t) (N := hc.CN t)
    (L := LB M Q B) (L' := LB M Q (conjSubgroup r B)) (T := T) (r := r)
    (fun s hs' x hx => (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 (hc.Rt_le_M t hs')) x).mp hx)
    sec39_Q_le_LB (fun x hx => (Ctx.mem_CN.mp hx).1) (le_Rt (LB M Q B) ht) hr
    (hc.LB_conj hrM) (fun s hs' x hx => hc.CN_conj_mem ht hs' hx)
    (fun h hh n' hn'' x hx => (Subgroup.mem_normalizer_iff.mp
      (hc.CN_normalizes_conj_LB h35 ht hh hn'') x).mp hx)
    hc.commutator_LB_le_Q hN hgenR hT

end CFSG.RankThree.GF2n.Stroth80
