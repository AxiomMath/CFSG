module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.Quasithin.Background.ConjugateSectionAction
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513LowNat
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

theorem s16h_sl4_engine_b_involution_swap
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
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {s : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hs : s ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hsq : s ^ 2 = 1) (hs1 : s ≠ 1)
    (hsN : s ∉ Subgroup.normalizer
      ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))) :
    2 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  let W := Vtil ⊥ V h.hyp151.isElemAbelian
  have hV := h.hyp151.isElemAbelian
  let A : Subgroup (MulAut W) := Mbar D.M ⊥ V hV
  let H : Subgroup (MulAut W) := lBar ⊥ V hV L
  let U : Subgroup W := commSub (⊤ : Subgroup W) H
  let Z : Subgroup W := commSub (⊤ : Subgroup W) H ⊓ fixV H
  have hcross : ∀ g ∈ A, g ∉ Subgroup.normalizer (H : Set (MulAut W)) →
      commSub (commSub (⊤ : Subgroup W) H) (H.map (MulAut.conj g).toMonoidHom) = ⊥ := by
    intro g hg hgn
    simpa only [A, H] using (hW.2.1 g hg hgn).2
  have hmove : E3.mQuot U Z ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers s)) := by
    have hmap_one : H.map (MulAut.conj (1 : MulAut W)).toMonoidHom = H := by
      ext x
      simp [MulAut.conj_apply]
    have hnot : s ∉ Subgroup.normalizer
        (H.map (MulAut.conj (1 : MulAut W)).toMonoidHom : Set (MulAut W)) := by
      simpa only [H, hmap_one] using hsN
    have h := CFSG.Quasithin.ConjugateSection.mQuot_le_rk_of_not_mem_normalizer
      (W := W) (A := A) (H := H) (a := 1) (t := s) hcross (Subgroup.one_mem A) hs hsq hnot
    simpa only [U, Z, hmap_one] using h
  have hrowU : Z ≤ U := by
    obtain ⟨_, _, _, _, _, _, hZU, _, _, _, _, _, _, _, _, _⟩ := hrow.2
    simpa only [U, Z, H] using hZU
  have hcard : Nat.card U = (2 ^ 2) ^ 2 * Nat.card Z := by
    have h := CFSG.Quasithin.H13.card_sec_of_binaryNaturalSL
      (H := H) (U := U) (Z := Z) (d := 2) (a := 2) (by simpa only [H, U, Z] using hrow.2)
    simpa using h
  have hrel : Z.relIndex U = 16 := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := U)
    rw [inf_eq_left.mpr hrowU, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by simpa using h)
  have hmq : E3.mQuot U Z = 4 := by
    unfold E3.mQuot
    rw [hrel]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
  have h4 : 4 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers s)) := by
    rw [hmq] at hmove
    exact hmove
  have h4' : 4 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
    rwa [← commV_eq_commSub, ← rkIdx_fixV_zpowers] at h4
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
