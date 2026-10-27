module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAABAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAABAAB
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]


variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_bb2bababba_central_conj_rank_of_not_normalizer
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∈ centSub (commSub ⊤ L))
    {g : MulAut W} (hg : g ∈ A)
    (hgN : g ∉ normalizer (L : Set (MulAut W)))
    (hne : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥) :
    3 ≤ rk ↥(commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ)) := by
  by_cases hstab : τ ∈ stabSub ((commSub ⊤ L).map g.toMonoidHom)
  · exact s16h_e3_l3_central_conj_comm_rank_stab hW ht ht2 ht1 htr hconc hcomp hthin hZ hL3 hd2 hτ
      hτ2 hτ1 hτN hτC hg hgN hstab hne
  · exact s16h_e3_l3_central_conj_comm_rank_move hW ht ht2 ht1 htr hconc hcomp hthin hZ hL3 hd2 hτ
      hτ2 hτ1 hτN hτC hg hgN hstab hne

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_bb2bababba_central_conj_rank_le_two
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∈ centSub (commSub ⊤ L))
    {g : MulAut W} (hg : g ∈ A)
    (hne : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥) :
    3 ≤ rk ↥(commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ)) := by
  by_cases hgN : g ∈ normalizer (L : Set (MulAut W))
  · exfalso
    have hgU : g ∈ stabSub (⊤ : Subgroup W) := mem_stabSub.mpr (fun _ => by simp)
    have hgstab : g ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
      StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) hgU hgN
    have hmap : (commSub (⊤ : Subgroup W) L).map g.toMonoidHom =
        commSub (⊤ : Subgroup W) L :=
      (StabLat.mem_stabSub_iff_map).mp hgstab
    have hfix : commSub (⊤ : Subgroup W) L ≤ fixV (Subgroup.zpowers τ) := by
      intro u hu
      rw [mem_fixV_zpowers_iff_apply]
      exact (mem_centSub.mp hτC) u hu
    refine hne ?_
    rw [hmap]
    exact commSub_eq_bot_iff.mpr hfix
  · exact s16h_e3_l3_bb2bababba_central_conj_rank_of_not_normalizer hW ht ht2 ht1 htr hconc hcomp
      hthin hZ hL3 hd2 hτ hτ2 hτ1 hτN hτC hg hgN hne

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_bb2bababba_rank_normalizer_of_central
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∈ centSub (commSub ⊤ L)) :
    3 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
  have hex : ∃ g ∈ A,
      commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥ := by
    by_contra h
    have h' : ∀ g, g ∈ A →
        commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) = ⊥ := by
      intro g hg
      by_contra hg'
      exact h ⟨g, hg, hg'⟩
    have hfix : ∀ g ∈ A,
        (commSub ⊤ L).map g.toMonoidHom ≤ fixV (Subgroup.zpowers τ) :=
      fun g hg => commSub_eq_bot_iff.mp (h' g hg)
    have hF : fixV (Subgroup.zpowers τ) = ⊤ := by
      rw [← top_le_iff, ← hconc.1]
      apply iSup_le
      intro X
      apply iSup_le
      intro hX
      obtain ⟨a, ha, rfl⟩ := hX
      exact hfix a ha
    have hτeq : τ = 1 := by
      ext v
      have hv : v ∈ fixV (Subgroup.zpowers τ) := by rw [hF]; trivial
      simpa using mem_fixV_zpowers_iff_apply.mp hv
    exact hτ1 hτeq
  obtain ⟨g, hgA, hne⟩ := hex
  have hle : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≤
      commSub (⊤ : Subgroup W) (Subgroup.zpowers τ) := commSub_mono le_top le_rfl
  exact le_trans (s16h_e3_l3_bb2bababba_central_conj_rank_le_two hW ht ht2 ht1 htr hconc hcomp hthin
    hZ hL3 hd2 hτ hτ2 hτ1 hτN hτC hgA hne) (rk_mono hle)

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_bb2bababba_central_rank
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
      Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))))
    (hτC : τ ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    3 ≤ rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian))
      (Subgroup.zpowers τ)) := by
  have hV := h.hyp151.isElemAbelian
  have hpow : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  exact s16h_e3_l3_bb2bababba_rank_normalizer_of_central hpow ht ht2 ht1 htr hW hcomp
    hthin hZ hL3 hd2 hτ hτ2 hτ1 hτN hτC

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_bb2bababba_involution_rank_normalizer
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
  · exact s16h_e3_l3_bb2bababba_central_rank D S h hs2 ht ht2 ht1 htr hW hcomp
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
    have hfix := s16h_e3_l3_bb2bababba_fix_rank (W := Vtil ⊥ V hV) hpow hL3
      hτ2 hτ1 hτN hτC
    have h3 : 3 ≤ rk ↥(commSub (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L))
        (Subgroup.zpowers τ)) := by
      omega
    exact le_trans h3 (rk_mono (commSub_mono le_top le_rfl))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
