module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAAB
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_three_ne_bot_dim_le_two_involution_rank_normalizer
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hd2 : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2)
    {τ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hτ : τ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ Subgroup.normalizer (lBar ⊥ V h.hyp151.isElemAbelian L :
      Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))) :
    3 ≤ rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian))
      (Subgroup.zpowers τ)) := by
  have hV := h.hyp151.isElemAbelian
  have hpow : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  by_cases hτC : τ ∈ centSub (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L))
  · exact s16h_e3_l3_three_ne_bot_dim_le_two_central_rank D S h hs2 ht ht2 ht1 htr hW hcomp
      hthin hZ hL3 hd2 hτ hτ2 hτ1 hτN hτC
  · have hsum := s16h_e3_l3_three_sum_rank (W := Vtil ⊥ V hV) (lBar ⊥ V hV L)
      (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L))
      (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L) ⊓
        fixV (lBar ⊥ V hV L)) hL3
    have hτstab : τ ∈ stabSub (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L)) :=
      StabLat.mem_stabSub_commSub (X := lBar ⊥ V hV L) (Y := ⊤)
        (mem_stabSub.mpr (fun _ => by simp)) hτN
    have hUinv : ∀ x ∈ Subgroup.zpowers τ,
        ∀ w ∈ commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L),
        x w ∈ commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L) := by
      intro x hx w hw
      exact (mem_stabSub.mp ((Subgroup.zpowers_le.mpr hτstab) hx) w).mpr hw
    have hrank := rk_commSub_add_rk_inf_fixV (V := Vtil ⊥ V hV) (g := τ)
      (W := commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L)) hUinv
    have hfix := s16h_e3_l3_three_ne_bot_dim_le_two_fix_rank (W := Vtil ⊥ V hV) hpow hL3
      hτ2 hτ1 hτN hτC
    have h3 : 3 ≤ rk ↥(commSub (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L))
        (Subgroup.zpowers τ)) := by
      omega
    exact le_trans h3 (rk_mono (commSub_mono le_top le_rfl))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
