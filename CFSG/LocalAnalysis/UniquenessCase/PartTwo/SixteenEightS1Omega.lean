module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaComp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_om_fstarBar_equiv (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) :
    Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
      (Multiplicative (ZMod 3) × ↥(lBar V₀ V hV L))) := by
  exact s16e_omf_fstarBar_equiv D hx h4 h61 h127 h1217 hV hset hL hconc h

theorem s16e_s1_case5_of_omegaPlus (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) : Case168_5Star D V₀ V hV L := by
  refine ⟨s16e_om_fstarBar_equiv D hx h4 h61 h127 h1217 hV hset hL hconc h, h.1, ?_, ?_⟩
  · rw [← s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL h.2.2]
    exact h.2.1
  · exact s16e_om_sig_eq_three D hx h4 h61 h127 h1217 hV hset hL hconc h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
