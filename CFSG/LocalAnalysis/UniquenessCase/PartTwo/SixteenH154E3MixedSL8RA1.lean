module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA1B
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_z_TI
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
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    CFSG.CGT.Timmesfeld75.IsTI
      (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hZeq : v1Sub D.M ⊥ V hV L =
      wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) :=
    s16h_sl28_v1Sub_eq_z D h hs2 hxM hxn hZ0
  have hZV : wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) ≤ V :=
    inf_le_left.trans (preTil_le ⊥ V hV (wTil ⊥ V hV L))
  have hZab : IsElemAbelian 2 (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) :=
    CFSG.Open.IsElemAbelian.mono hV hZV
  have hZnorm : D.M ≤
      normalizer ((wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    rw [← hZeq]
    exact s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV
  refine s15_FiveTen_isTI_of_uniqueMax D hZab hZnorm ?_
  intro w hw hw1
  obtain ⟨E, hEM, hEp, hEnc, hEcent⟩ :=
    s16h_sl28_seven_z_noncyclic D h hs2 hrow hcomp hthin h7 hxM hxn hZ0 w hw hw1
  exact s16c34_uniqueMax_of_noncyclic D S.h61 h7 hEp hEnc (le_inf hEM hEcent) inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
