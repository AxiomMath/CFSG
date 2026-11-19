module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourConj
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

theorem s16h_sl28_seven_le_normalizer_of_odd
    (D : Data G) (_S : s16h_Std D) (_hσ : D.sig = D.sig1)
    (_hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (_ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (_ht2 : t ^ 2 = 1) (_ht1 : t ≠ 1) (_htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (_hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (_hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (_hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (_hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (_hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (_hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (_hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (_h7 : 7 ∈ D.sig)
    (E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hEM : E ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hEodd : Odd (Nat.card ↥E)) :
    E ≤ Subgroup.normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) := by
  have hV := h.hyp151.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil ⊥ V hV)) := lBar ⊥ V hV L
  let Mb : Subgroup (MulAut (Vtil ⊥ V hV)) := Mbar D.M ⊥ V hV
  have hcard : Set.ncard {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mb, X = Lb.map (MulAut.conj φ).toMonoidHom} ≤ 2 := by
    simpa [s15, lBar, Lb, Mb] using hs2.le
  intro m hmE
  have hmM : m ∈ Mb := hEM hmE
  have hoddm : Odd (orderOf m) :=
    Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E hmE)
  exact s15GapFour_mem_normalizer_of_odd Mb Lb hcard hmM hoddm (pow_orderOf_eq_one m)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
