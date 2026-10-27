module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Rank3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r38m3_pRank_le_add {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hP : PairFacts M V₀ V) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p M ≤
      CFSG.Open.pRank p (F11.CTilde M V₀ V) + CFSG.Open.pRank p (Mbar M V₀ V hV) := by
  have hp1 : 1 < p := hp.one_lt
  have hMs : M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hCM : F11.CTilde M V₀ V ≤ M := fun g hg =>
    ((mem_cTilde_iff hV hP.le_normalizer).1 hg).1
  have h := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hp (barHom V₀ V hV hMs) ⊤
  rw [top_inf_eq, ker_barHom V₀ V hV hP.le_normalizer hMs, ← MonoidHom.range_eq_map,
    range_barHom V₀ V hV hMs] at h
  have h1 : CFSG.Open.pRank p M = CFSG.Open.pRank p (⊤ : Subgroup ↥M) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup M
  have h2 : CFSG.Open.pRank p ((F11.CTilde M V₀ V).subgroupOf M) ≤
      CFSG.Open.pRank p (F11.CTilde M V₀ V) := by
    have h3 := CFSG.SectionRank.pRank_le_map hp1 M.subtype M.subtype_injective
      ((F11.CTilde M V₀ V).subgroupOf M)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCM] at h3
  show CFSG.Open.pRank p M ≤
    CFSG.Open.pRank p (F11.CTilde M V₀ V) + CFSG.Open.pRank p (barSub V₀ V hV M)
  omega

theorem r16_38_m3Gap_of_r638 (D : Data G) (h127 : R127 D) (h638 : UC6.R6_38 D) :
    R16_38_m3Gap D := by
  intro _ _ _ _ h61 hext _ V₀ V L hV hS hc _ _ _ _ hne _
  have hsig : D.sig = {3} := hc.2.2
  have h3sig : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have hm : Case1633 D V₀ V hV L 3 := Or.inr ⟨hc, rfl⟩
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  have hSK8 : Nat.card S.K = 8 := by rw [hSK]; norm_num
  have hΩ : Nat.card S.omega = 254016 := by
    rw [hSω, Om8Excl.card_isOmegaPlus_four (by norm_num : 2 ≤ 3) hc.1]
    norm_num
  have h16 : Hyp16 D V₀ V := hS.setting.hyp16
  have hP : PairFacts D.M V₀ V := h16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hrN : (barHom V₀ V hV hMs).range ≤ OmegaModel.omegaNorm S := by
    rw [range_barHom V₀ V hV hMs]
    exact Mbar_le_normalizer_lBar hS S hSω
  have hOp : F10.OpRes 3 D.M = D.M := h638 3 Nat.prime_three (by norm_num) (Or.inl h3sig)
  haveI hNorm : ((OmegaModel.linSub S).comap (barHom V₀ V hV hMs)).Normal :=
    OmegaModel.normal_comap_linSub S _ hrN
  have hq : IsPGroup 3 (↥D.M ⧸ (OmegaModel.linSub S).comap (barHom V₀ V hV hMs)) :=
    OmegaModel.isPGroup_quotient_comap_linSub S hSK8 _ hrN
  have htop : (OmegaModel.linSub S).comap (barHom V₀ V hV hMs) = ⊤ :=
    UC6.eq_top_of_isPGroup_quotient_of_opRes_eq_uc6 Nat.prime_three hOp _ hq
  have hMlin : Mbar D.M V₀ V hV ≤ OmegaModel.omegaNorm S ⊓ OmegaModel.linSub S := by
    change barSub V₀ V hV D.M ≤ _
    rw [← range_barHom V₀ V hV hMs]
    rintro _ ⟨m, rfl⟩
    refine ⟨hrN ⟨m, rfl⟩, ?_⟩
    have hm' : m ∈ (OmegaModel.linSub S).comap (barHom V₀ V hV hMs) := by rw [htop]; trivial
    exact hm'
  have hb : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEM hE => ?_
    have h9 := S.card_le_nine_of_isElemAbelian_le_normalizer_inf_linSub hSK8 hΩ hE
      (hEM.trans hMlin)
    simpa using h9
  have ha : CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) ≤ 1 :=
    uc22p22q_pRank_ctilde_le_one D h61 (Hyp125.hyp11 h127 h16.hyp125)
      (Sixteen21.card_le_four_of_hyp16 h16) h3sig
  have hadd := r38m3_pRank_le_add hV hP Nat.prime_three
  have hlt : 3 < CFSG.Open.evenRank G := lt_of_le_of_ne D.standing.rank (Ne.symm hne)
  have h4 := hext.four_le hlt 3 h3sig
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
