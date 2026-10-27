module

public import CFSG.RankThree.PartOne.HNB.TransportFixed

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly (InCatalog)

theorem hnSuccessorTransport_of_inputs (hS : SchreierFor InCatalog) (hbridge : BridgeHyp)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hN : HNNativeFive) :
    HNRed.HNSuccessorTransport := by
  intro G _ _ A h L hL hLHN
  obtain ⟨e⟩ := hLHN
  obtain ⟨d⟩ := exists_actorGroup h hL.1.1 hN e
  obtain ⟨a⟩ := exists_actor h.2.2.2.1 d
  obtain ⟨s⟩ := Successor.exists_successor hS h a
  have hq := s.isQuasisimple_X hbridge hK h
  exact ⟨a.H, s.X, s.beta h, s.Lambda h, s.bar a.KH, s.bar a.YH, innerPart s.Phi s.RN,
    a.twoLocalOddRank_H h, hq, s.catalog hbridge hK h, s.isElementaryAbelian_Lambda h,
    s.card_Lambda h hq, s.beta_mem_Lambda h, s.fiveFixedPSU3 hbridge hK h,
    s.bar_YH_le_bar_KH, s.nonempty_bar_YH_equiv_sl2, s.U_ne_bot hbridge hK h,
    s.isPGroup_U hbridge hK h, fun _ hu => s.beta_mem_U h hu,
    fun _ hy _ hu => s.Y_conj_mem_U hy hu, s.closure_U hbridge hK h⟩

end CFSG.RankThree.PartOne.HNB
