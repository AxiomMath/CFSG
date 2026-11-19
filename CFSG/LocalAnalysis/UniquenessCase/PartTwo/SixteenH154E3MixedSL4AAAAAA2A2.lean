module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA2A2A
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

theorem s16h_sl4_quotient_fixV
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
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (_hxM : x ∈ D.M) (_hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {φ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (_hφM : φ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (_hφ3 : orderOf φ = 3)
    (hcent : ∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian L, φ * a = a * φ)
    (_hcentx : ∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x), φ * a = a * φ)
    (hnontriv : ∃ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L, φ z ≠ z) :
    ∀ v ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L),
      φ v * v⁻¹ ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L) →
      v ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L) := by
  refine s16h_sl4_quotient_fixV_aux (W := Vtil ⊥ V h.hyp151.isElemAbelian)
    (L := lBar ⊥ V h.hyp151.isElemAbelian L) hrow hcent ?_
  intro hmem
  obtain ⟨z, hz, hzφ⟩ := hnontriv
  exact hzφ (mem_centSub.mp hmem z (by simpa [wTil, lBar] using hz))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
