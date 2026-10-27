module

public import CFSG.RankThree.GF2n.Tim81.Sections4to7
public import CFSG.RankThree.GF2n.Tim81.Sec6.Basic
public import CFSG.RankThree.GF2n.Tim81.Sec6.S63
public import CFSG.RankThree.GF2n.Tim81.Sec6.S65
public import CFSG.RankThree.GF2n.Tim81.Recog.GR
import CFSG.RankThree.GF2n.Tim81.Sec6.S64
import CFSG.RankThree.GF2n.Tim81.Sec6.S65End

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

theorem sec65Statement_of (hB : Timmesfeld.Bridge.OddTranspBender)
    (h18 : Timmesfeld.Bridge.CommonNeighbourStmt)
    (hT : Timmesfeld.Transvection.SubgroupTransvectionStatement) :
    Sec65Statement := by
  intro G _ _ M V hS n hn hn3
  have h60 := hS.stmt60
  have hnc := hS.stmt63 hS.stmt61b n hn hn3
  have hSig := hS.stmt64 n hn hn3 hnc
  have hF := hS.normalClosure_eq h60
  have hpair := hS.omega_pairs hB h60 h18 (hS.stmt65a_of hB n hn hn3 hnc hSig) hSig hF
  refine hS.unitaryConclusion_of_omega h60 hT hF hpair fun B hB hBV hVB => ?_
  have hBC : B ≤ Subgroup.centralizer (V : Set G) := by
    rwa [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  have hBM : B ≤ M := by
    rw [← hS.sec5.toRootHyp.toHyp.normalizer_eq]
    exact hBC.trans (Subgroup.centralizer_le_normalizer _)
  exact (hSig B hB hBM).resolve_left hBV

end CFSG.RankThree.GF2n.Tim81
