module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB2B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Abstract

variable {W : Type} [CommGroup W]

private theorem s16h_e3_l3_bb2cab_sum_rank [Finite W] (L : Subgroup (MulAut W)) (U Z : Subgroup W)
    (h : s16h_H5L3Sum L U Z 3) : rk ↥Z + 3 ≤ rk ↥U := by
  obtain ⟨-, hsum⟩ := h
  have hm : ∀ I : Subgroup W, BinaryNaturalSL L I Z 3 1 → rk ↥I = rk ↥Z + 3 := by
    intro I hI
    obtain ⟨K, hField, hFin, hK, hreal⟩ := hI
    have := s16fh_rk_of_realizes_nat hK hreal
    simpa using this
  have hge := s16fh_rk_sumOfNat_ge (N := fun H I Z => BinaryNaturalSL H I Z 3 1) hsum hm
  omega

end Abstract

section Setting

theorem s16h_e3_l3_three_ne_bot_dim_le_two_involution_rank_not_normalizer
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
    (hτn : τ ∉ Subgroup.normalizer (lBar ⊥ V h.hyp151.isElemAbelian L :
      Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))) :
    3 ≤ rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian))
      (Subgroup.zpowers τ)) := by
  have hV := h.hyp151.isElemAbelian
  have hout := s16h_e3_l3_two_outside_swap_rank D S h ht hW hτ hτ2 hτn
  have h3 := s16h_e3_l3_bb2cab_sum_rank (W := Vtil ⊥ V hV) (lBar ⊥ V hV L)
    (commSub ⊤ (lBar ⊥ V hV L))
    (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) hL3
  omega

end Setting

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
