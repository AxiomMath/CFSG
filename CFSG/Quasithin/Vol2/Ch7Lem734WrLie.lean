module

public import CFSG.Quasithin.Vol2.Ch7Lem734Wr
public import CFSG.Quasithin.Vol2.Ch4Sec4W4414Lie
public import CFSG.Quasithin.Vol2.Ch3T326H2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem local_structure_wreath_lie (h4414 : Stmt4_4_14Lie) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) (hIV : I = fsuV T I)
    (hTI : IsTISetUnder (fsuV T I) (fsuM T L)) :
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H →
      (∃ K ∈ cComp H, H = K ⊔ T ∧ E2.E22LieCases H T (H ⊓ fsuM T L) K) →
      H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G) ∧
        H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (H ⊓ fsuM T L) := by
  intro H hH hLie
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hloc1 := inf_fsuM_eq_of_ti hC58 h317 h37 h38 h39 h3228 hyp hTI hH
  have hcen := (center_facts_fsu hC58 h317 h37 h38 h39 h3228 hyp hH).2
  refine ⟨hloc1, ?_⟩
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
    hyp.fsu.sylow hyp.fsu.maximal
  obtain ⟨hVX, hred, -⟩ := h3228 G T L I hyp.fsu
  have hcomm := commutator_fsuV_fsuL0 hyp.fsu hN
  rcases h4414 G T (fsuM T L) L (fsuV T I) H hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.sylow hU.1.1 (le_sup_right.trans hU.1.2) hyp.fsu.maximal hyp.fsu.faithful
      (le_sup_left.trans hU.1.2) hyp.fsu.quasisimple hVX hred hH
      (by rw [hcomm]; exact fsuV_ne_bot hyp.fsu)
      (fsuV_eq_conjClosure_of_eq hyp hIV hV hN hcen)
      (by rw [hcomm]; exact not_isFFModule_autOn_sup h37 h38 h39 hyp hV hN) hLie with
    ⟨h2c, hfaith⟩ | ⟨n, hn1, -, h2⟩ | ⟨-, h3⟩
  · exact inf_centralizer_le_of_faithful' h37 h38 h3228 hyp hrow.1 hloc1 h2c hfaith
  · rw [hcomm] at h2
    exact (not_orth hyp hn1 h2).elim
  · rw [hcomm] at h3
    exfalso
    obtain ⟨hc, h3⟩ := h3
    have h64 := Fano.FanoCoreModule.card h3
    rw [card_fsuV_wreath hrow] at h64
    norm_num at h64

theorem local_structure_wreath_lie_of (h326 : Stmt3_2_6C) (h4414 : Stmt4_4_14Lie)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I)
    [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I) :
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H →
      (∃ K ∈ cComp H, H = K ⊔ T ∧ E2.E22LieCases H T (H ⊓ fsuM T L) K) →
      H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G) ∧
        H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (H ⊓ fsuM T L) := by
  rcases stmt3_2_6Lt_of_C h326 G T L I hyp.fsu hrow.1 with ⟨-, hIV, hVM, -⟩ | h3
  · have hTI : IsTISetUnder (fsuV T I) (fsuM T L) := by
      intro g hg hgn
      exfalso
      apply hgn
      rw [hVM]
      exact le_normalizer_conjClosure _ _ hg
    exact local_structure_wreath_lie h4414 hC58 h317 h37 h38 h39 h3228 hyp hrow hIV hTI
  · exact absurd ⟨hrow.1, h3⟩ hyp.notThree

end CFSG.Quasithin.H13
