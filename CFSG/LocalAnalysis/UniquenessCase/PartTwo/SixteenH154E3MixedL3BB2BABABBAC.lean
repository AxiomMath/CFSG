module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2BB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2BABABBACA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2BABABBACB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_bb2bababba_parabolic
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
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowL3 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hd2 : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2)
    (hsig : D.sig = {3}) :
    ∃ (J : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) (a : ℕ),
      J ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧
      barSub ⊥ V h.hyp151.isElemAbelian D.T ≤ J ∧
      Nat.card ↥J = 2 ^ a * 9 ∧
      (∀ x ∈ J, x ^ 9 = 1 → x ^ 3 = 1) := by
  obtain ⟨B, hBle, hBcard, hBexp, hBT⟩ :=
    s16h_e3_l3_bb2bababba_parabolic_data D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin
      hZ hbad hrow hL3 hd2 hsig
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hTstab : D.T ≤ stabTil ⊥ V := D.sylowM.le.trans hMs
  have hT2 : IsPGroup 2 ↥(barSub ⊥ V hV D.T) := by
    unfold barSub
    exact (D.sylowM.isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe hTstab).symm).map (actTil ⊥ V hV)
  exact s16h_e3_l3_bb2bababba_two_three_of_normalized
    (barSub_mono ⊥ V hV D.sylowM.le) hBle hT2 hBcard hBexp hBT

theorem s16h_e3_l3_bb2bababba_permuting
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
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowL3 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hd2 : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2)
    (hsig : D.sig = {3}) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧ Nat.card ↥Y = 9 ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧ Permutes Y D.T := by
  have h3C := s16h_e3_l3_three_ne_bot_dim_le_two_not_dvd_CTilde D S hσ hJP h hs2 ht ht2
    ht1 htr hW hcomp hthin hZ hbad hrow hL3 hd2 hsig
  obtain ⟨J, a, hJ, hTJ, hJcard, hJexp⟩ :=
    s16h_e3_l3_bb2bababba_parabolic D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin
      hZ hbad hrow hL3 hd2 hsig
  exact s16h_e3_permuting_lift D h.hyp16.hyp125 h3C hJ hTJ hJcard hJexp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
