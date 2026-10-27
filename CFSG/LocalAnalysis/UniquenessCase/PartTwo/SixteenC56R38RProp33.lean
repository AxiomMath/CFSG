module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38M3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RTheta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem evenRank_le_three_of_case167_5 (D : Data G) (hext : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_5 D V₀ V hV L) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hK : Nat.card S.K = 4) :
    CFSG.Open.evenRank G ≤ 3 := by
  by_contra hlt
  have hlt' : 3 < CFSG.Open.evenRank G := not_le.mp hlt
  have hsig : D.sig = {5} := hc.2.2
  have h5sig : 5 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 5
  have h16 : Hyp16 D V₀ V := hS.setting.hyp16
  have hP : PairFacts D.M V₀ V := h16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hMbN : Mbar D.M V₀ V hV ≤ OmegaModel.omegaNorm S := Mbar_le_normalizer_lBar hS S hSω
  have hb : CFSG.Open.pRank 5 (Mbar D.M V₀ V hV) ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEM hE => ?_
    have h25 := S.card_dvd_of_isPGroup_five hK hE.isPGroup (hEM.trans hMbN)
    exact Nat.le_of_dvd (by norm_num) h25
  have ha : CFSG.Open.pRank 5 (F11.CTilde D.M V₀ V) ≤ 1 :=
    uc22p22q_pRank_ctilde_le_one D h61 (Hyp125.hyp11 h127 h16.hyp125)
      (Sixteen21.card_le_four_of_hyp16 h16) h5sig
  have hadd := r38m3_pRank_le_add hV hP (by norm_num : Nat.Prime 5)
  have h4 := hext.four_le hlt' 5 h5sig
  omega

theorem pRank_three_le_three_of_case167_5 (D : Data G) (hext : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_5 D V₀ V hV L) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hK : Nat.card S.K = 4) :
    CFSG.Open.pRank 3 D.M ≤ 3 :=
  (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) D.M D.maxLocal.1).trans
    (evenRank_le_three_of_case167_5 D hext h61 h127 hS hc S hSω hK)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
