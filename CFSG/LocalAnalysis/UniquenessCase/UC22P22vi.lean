module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22va
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vd
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vg
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vh
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vk
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22vi_s22_11_of (D : Data G) (Ch : Choice2011 G) (h516 : F05.K516K)
    (h1110 : R1110W D) (h119 : R119W D) (h77 : F07.R77Eq D) (h63 : UC6.R6_3 D) (h67 : UC6.R6_7 D)
    (hSg : UC6S846.SigmaStd D) (hV : S22_V D Ch) (h8 : S22_8 D Ch) (h9 : S22_9 D Ch)
    (h10 : S22_10 D Ch) (h1117 : S21_17 D Ch) (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) :
    S22_11 D Ch := by
  intro h1930 c
  have hel : IsElemAbelian 2 c.V := (uc22p22o_inCalV_of_le_U D c.hVU c.hVne c.hVM).2.2.2
  have hO2 : CFSG.pCore 2 (MBar D.M c.V) = ⊥ :=
    (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 (hV h1930 c).1.2.2
  have hcyc : IsCyclic ↥(CFSG.fittingSubgroup ↥(_root_.commutator (MBar D.M c.V))) := by
    by_contra hF
    obtain ⟨q, hq, hq2, hqα, P, hP, hmin⟩ := uc22p22va_exists_minimal_calQ hO2 hF
    have hinj : c.B0 ⊓ centralizer (c.V : Set G) = ⊥ :=
      uc22p22vk_b0_inter_ker D Ch h1930 hV h8 h10 h1110 h63 h67 h77 hSg c q hq hq2 P hP
    obtain ⟨Vmod, i1, i2, i3, e, ρ, hc⟩ := uc22br4_exists_conjModule D.M c.V c.hVM hel
    have hTM : D.T ≤ D.M := D.sylowM.le
    obtain ⟨hT2, hBab, hBodd, hBperm⟩ :=
      uc22p22vd_mbarImage_basic D.M c.V D.T c.B0 hTM c.hBM
    let c0 : Ctx21 D Ch := { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl }
    obtain ⟨-, -, B', C', -, -, -, -, -, hperm0, -, -⟩ := c.hB0
    have H51 : F05.Hyp51 q P (mbarImage D.M c.V D.T) (mbarImage D.M c.V c.B0) c.n :=
      { prime := hq
        odd := hq2
        pGroup := hP.2.2.1
        exponent := hP.2.2.2.1
        classTwo := hP.2.2.2.2.1
        twoGroup := hT2 D.sylowM.isPGroup
        abelian := hBab c.hB0.2.1
        oddOrder := hBodd (uc22p22f_odd_card_B c0)
        permutes := hBperm hperm0
        acts := by
          rw [Subgroup.normalizer_eq_top_iff.mpr hP.1]
          exact le_top
        cyclic := fun b hb hb1 =>
          uc22p22vk_hyp515_cyclic D Ch h1930 hV h8 h10 h1110 h63 h67 h77 hSg c q hqα P hP b hb hb1
        eGt := hn3 c
        piB := fun r hr => uc22p22vd_hyp51_piB D Ch h1930 c hinj r hr
        expB := (uc22p22vd_hyp51_exp_normT D Ch h1930 c).1
        normT := (uc22p22vd_hyp51_exp_normT D Ch h1930 c).2 }
    have H53 : F05.Hyp53 ρ q P (mbarImage D.M c.V D.T) (mbarImage D.M c.V c.B0) :=
      { faithful := uc22br4_injective D.M c.V c.hVM e ρ hc
        irreducible := (uc22br4_isIrreducible_iff D.M c.V c.hVM e ρ hc).2 ⟨c.hVne, c.hVirr⟩
        sylow := uc22p22vd_isSylow_mbarImage D c.V
        centralizesZ := uc22p22vd_hyp53_centralizesZ D Ch h1930 c e ρ hc
        normal := hP.1
        rank := uc22p22u_two_le_pRank hq hq2 hP.2.2.1 hP.2.1
        minimal := hmin }
    have H515 : F05.Hyp515 (mbarImage D.M c.V c.B0) :=
      { cyclic := fun q' hq'α Q hQ b hb hb1 =>
          uc22p22vk_hyp515_cyclic D Ch h1930 hV h8 h10 h1110 h63 h67 h77 hSg c q' hq'α Q hQ b hb hb1
        components := uc22p22vg_hyp515_components D Ch h1930 hV h119 h1117 c }
    rcases h516 (MBar D.M c.V) (uc22br4_isKGroup_mbar_data_catalog D c.V) Vmod ρ q P
        (mbarImage D.M c.V D.T) (mbarImage D.M c.V c.B0) c.n H51 H53 H515 with h | h | ⟨hPB, h3, hninv⟩
    · exact uc22p22vh_contra1 D Ch h1930 h9 c e ρ hc h
    · exact uc22p22vh_contra2 D Ch h1930 hV h8 h10 h1110 hSg c h
    · exact hninv (uc22p22vh_contra3 D Ch h1930 hV h8 h10 h1110 hSg c q hq hq2 P hP hPB h3)
  exact ⟨hcyc, uc22p22vh_centralized_of_cyclic D Ch h1930 hV c hcyc⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
