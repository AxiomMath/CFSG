module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_z0_le_centralizer
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
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x ≤
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hxinvM : x⁻¹ ∈ D.M := D.M.inv_mem hxM
  have hxninv : x⁻¹ ∉ nBar D.M ⊥ V hV L := fun hh =>
    hxn ((nBar D.M ⊥ V hV L).inv_mem_iff.mp hh)
  have hE : conjSubgroup L x⁻¹ ≤ stabTil ⊥ V := by
    refine (E3.conjSubgroup_mono_left x⁻¹ (h.hyp151.le.trans hMs)).trans ?_
    rw [show conjSubgroup (stabTil ⊥ V) x⁻¹ = stabTil ⊥ V from
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hMs hxinvM))]
  have hcomm : commSub (wTil ⊥ V hV L) (barSub ⊥ V hV (conjSubgroup L x⁻¹)) = ⊥ :=
    (h.hyp151.commute x⁻¹ hxinvM hxninv).2
  have hWle : wSub ⊥ V hV L ≤ preTil ⊥ V hV (fixV (barSub ⊥ V hV (conjSubgroup L x⁻¹))) :=
    s16c34_wSub_le_preTil_fixV hV hcomm
  have hLcentW : conjSubgroup L x⁻¹ ≤ Subgroup.centralizer (wSub ⊥ V hV L : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwV : w ∈ V := preTil_le ⊥ V hV _ (hWle hw)
    have h1 :=
      (s15_Glue_mem_preTil_fixV_iff ⊥ V (conjSubgroup L x⁻¹) hV hE hwV).1 (hWle hw) e he
    rw [Subgroup.mem_bot] at h1
    have h2 : e * w * e⁻¹ = w := mul_inv_eq_one.1 h1
    have h3 : e * w = w * e := by
      calc e * w = (e * w * e⁻¹) * e := by group
        _ = w * e := by rw [h2]
    exact h3.symm
  have hLcentWx : L ≤ Subgroup.centralizer
      (conjSubgroup (wSub ⊥ V hV L) x : Set G) := by
    have hmono := E3.conjSubgroup_mono_left x hLcentW
    rw [E3.conjSubgroup_inv_conj L x, E3.conjSubgroup_centralizer (wSub ⊥ V hV L) x] at hmono
    exact hmono
  have hWxcentL : conjSubgroup (wSub ⊥ V hV L) x ≤ Subgroup.centralizer (L : Set G) :=
    (Subgroup.le_centralizer_iff (H := L)
      (K := conjSubgroup (wSub ⊥ V hV L) x)).1 hLcentWx
  exact le_inf inf_le_left (inf_le_right.trans hWxcentL)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
