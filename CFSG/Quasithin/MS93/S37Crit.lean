module

public import CFSG.Quasithin.MS93.S36Frat
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S36

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem qv_inr (h : PUHyp M T L) (ψ : MulAut ↥T) :
    Qv (puAmalgam h.le) ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) =
      imM h.le (tImage ψ (pCoreOf 2 M)) := by
  rw [qv_smul, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
    imM_map_conj_inr h.le ψ h.pCore_le]

theorem exists_critical (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2) :
    ∃ ψ : MulAut ↥T, ¬ Z0q M T ≤ tImage ψ (pCoreOf 2 M) := by
  obtain ⟨α', hc, hgeo⟩ := exists_isCritical_geo _ h.hyp20 h.critDist_pos (isMVtx_baseA _)
    (adj_baseA_baseB (puAmalgam h.le))
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 2 := hc.2.1.trans hb
  have hadj : (puAmalgam h.le).treeGraph.Adj (baseB _) α' := by
    have := adj_geo (puAmalgam h.le) (u := baseA _) (w := α') (i := 1) (by omega)
    rwa [hgeo, geo_of_le _ (by omega)] at this
  obtain ⟨ψ, rfl⟩ := (puAmalgam.adj_baseB_iff_mulAut h.le α').mp hadj
  refine ⟨ψ, fun hle => hc.2.2 ?_⟩
  rw [qv_inr h, puAmalgam.zm_baseA, imM_le_imM_iff h.le (Z0q_le M T)]
  exact hle

end CFSG.Quasithin.MS93.S37
