module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA2AAA
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_zmod_not_bad_of_rk_le_two
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (h7 : 7 ∈ D.sig)
    (hrk : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2) :
    ¬ (∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2) := by
  intro hbad
  have hV := h.hyp151.isElemAbelian
  have hcfg : s16h_H5Cfg (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one ⊥ V hV, ht, ht2, ht1, htr, hW, hcomp, hthin⟩
  have hBB : s16h_BlockBound (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) 7 1 :=
    s16h_H5_SL2_eight_seven_block hcfg hrow hZ hrk
  have hpp := D.sig_prime 7 h7
  obtain ⟨E, hEM, hE, hEcard⟩ := c23_exists_elemAbelian_card_pow (p := 7) (M := D.M) (k := 3)
    (by norm_num) (by rw [UC6.groupPRank_eq_pRank]; exact S.hx.three_le 7 h7)
  have hEn : barSub ⊥ V hV E ≤
      normalizer (barSub ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) :=
    s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 hs2.le
      (hpp.1.odd_of_ne_two hpp.2) hEM hE
  have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 (c := 1)
    hBB hEM hE hEn
  rw [hEcard] at hcard
  have h49 : 7 ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M ⊥ V hV
      (centSub (wTil ⊥ V hV L))) := by
    have h' : 7 * 7 ^ 2 ≤ 7 * Nat.card ↥(E ⊓ preBarSub D.M ⊥ V hV
        (centSub (wTil ⊥ V hV L))) := by
      calc 7 * 7 ^ 2 = 7 ^ 3 := by ring
        _ ≤ _ := by simpa using hcard
    exact Nat.le_of_mul_le_mul_left h' (by norm_num)
  exact not_lt.2 h49 (hbad 7 h7 E hEM hE)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
