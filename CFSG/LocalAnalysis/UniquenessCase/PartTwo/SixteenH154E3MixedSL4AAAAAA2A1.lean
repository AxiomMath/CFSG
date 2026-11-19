module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.Adapters.StatedSLPerfect
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

theorem s16h_sl4_commSub_commSub_self
    (D : Data G) (_S : s16h_Std D) (_hσ : D.sig = D.sig1)
    (_hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (_hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
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
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (_hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    commSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (lBar ⊥ V h.hyp151.isElemAbelian L) =
      commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hrow.1
  let : Field K := hKf
  let : Finite K := hKfin
  have hK4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
  have : Group.IsPerfect ↥(StatedSL 2 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
  have hperf : Group.IsPerfect ↥(lBar ⊥ V h.hyp151.isElemAbelian L) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact s16jp_commSub_commSub hperf (Y := ⊤) (fun l _ y _ => Subgroup.mem_top (l y))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
